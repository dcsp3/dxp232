# API Refinement Properties

Having defined API refinement, we now establish its basic algebraic structure.

As with schema and endpoint refinement, the goal is to show that API refinement forms a preorder:

- Reflexivity: every well-formed API safely refines itself.
- Transitivity: safe API evolutions compose.

These properties justify treating API refinement as a principled notion of backwards-compatible evolution. In particular, they ensure that compatibility is stable under multi-step version changes.

All proofs proceed structurally, lifting the corresponding results from schema and endpoint refinement to the API level.

```agda
module Semantics.APIRefinementProperties where

open import Prelude
open import Syntax.Syntax
open import Syntax.Decidable

open import WellFormed.Core

open import Semantics.Variance

open import Semantics.SchemaRefinement
open import Semantics.SchemaRefinementProperties

open import Semantics.EndpointRefinement
open import Semantics.EndpointRefinementProperties

open import Semantics.APIRefinement

open Σ using (fst ; snd)
```

---

## 1. Reflexivity

Every well-formed API safely refines itself.

Reflexivity follows structurally from reflexivity of schema and endpoint refinement. We first establish reflexivity for component lists and endpoint lists, then combine them into the main API-level result.

---

### 1.1 Component reflexivity

Component refinement iterates over the old component list and aligns entries via lookup. Reflexivity therefore follows by recursion over the list, using `⊑Co-refl` for schemas.

```agda
Components⊑-weaken :
    ∀ {k s cs new}
  → k ∉ keys cs
  → Components⊑ cs new
  → Components⊑ cs ((k , s) :: new)

Components⊑-weaken {cs = []} _ tt = tt

Components⊑-weaken
  {k} {s} {cs = (k' , s') :: cs'} {new}
  (notin::_ k≢k' k∉tail)
  ( (t , (lkt , r)) , rest )
  =
  ( t , (lookupComponent-there k≢k' lkt , r) )
  , Components⊑-weaken k∉tail rest
```

```agda
Components⊑-refl :
  ∀ {cs}
  → Unique (keys cs)
  → All WFSchema (values cs)
  → Components⊑ cs cs

Components⊑-refl {cs = []} _ _ = tt

Components⊑-refl
  {cs = (k , s) :: cs'}
  (uniq::_ k∉tail uniqTail)
  (all::_ wfS wfTail)
  =
  ( s , (lookupComponent-here , ⊑Co-refl wfS) )
  , Components⊑-weaken
      k∉tail
      (Components⊑-refl uniqTail wfTail)
```

---

### 1.2 Endpoint Reflexivity

Endpoint list refinement mirrors the component case.
We prove reflexivity by recursion over the endpoint list, using `Endpoint⊑-refl` and a weakening lemma to skip fresh heads during lookup.

```agda
Endpoints⊑-weaken :
    ∀ {e es new}
  → (Endpoint.route e , Endpoint.method e) ∉ endpointKeys es
  → Endpoints⊑ es new
  → Endpoints⊑ es (e :: new)

Endpoints⊑-weaken {es = []} _ tt = tt
Endpoints⊑-weaken
  {e} {es = h :: es'} {new}
  (notin::_ head≢ tail∉)
  ( (e' , (lk , r)) , rest )
  =
  ( e' , (lookupEndpoint-there head≢ lk , r) )
  , Endpoints⊑-weaken tail∉ rest
```

```agda
Endpoints⊑-refl :
  ∀ {es}
  → Unique (endpointKeys es)
  → All WFEndpoint es
  → Endpoints⊑ es es

Endpoints⊑-refl {es = []} _ _ = tt
Endpoints⊑-refl
  {es = e :: es'}
  (uniq::_ e∉tail uniqTail)
  (all::_ wfE wfTail)
  =
  ( e , (lookupEndpoint-here , Endpoint⊑-refl wfE) )
  , Endpoints⊑-weaken
      e∉tail
      (Endpoints⊑-refl uniqTail wfTail)
```

---

### 1.3 API Reflexivity

API refinement is reflexive when both component and endpoint refinement are reflexive.

```agda
API⊑-refl :
  ∀ {a}
  → WFAPI a
  → API⊑ a a

API⊑-refl
  {a}
  (wf-api wfComps uniqComps wfPaths uniqPaths)
  =
  ⊑-api
    (wf-api wfComps uniqComps wfPaths uniqPaths)
    (wf-api wfComps uniqComps wfPaths uniqPaths)
    (Components⊑-refl uniqComps wfComps)
    (Endpoints⊑-refl uniqPaths wfPaths)
```

---

## 2. Transitivity

API refinement composes across versions.

If an API `a₀` safely refines `a₁`, and `a₁` safely refines `a₂`, then `a₀` safely refines `a₂`.

As in the lower layers, the proof proceeds structurally. We first establish transitivity for component refinement and endpoint refinement over lists, then combine them into the main API-level result.

The key step for components is transporting lookup across an intermediate list: if a component is preserved from `a₀` to `a₁`, and from `a₁` to `a₂`, then it is preserved from `a₀` to `a₂`.

---

### 2.1 Transporting component lookup

To compose component refinement, we must transport lookup across an intermediate component list.

If a component `(k , s)` appears in `cs`, and `cs ⊑ ds`, then looking up `k` in `ds` yields a schema `t` such that `s` refines `t`.

```agda
Components⊑-lookup :
    ∀ {cs ds k s}
  → Components⊑ cs ds
  → lookupComponent k cs ≡ just s
  → Σ Schema (λ t →
       lookupComponent k ds ≡ just t
     × Schema⊑ Co s t)

Components⊑-lookup {cs = []} _ ()

Components⊑-lookup
  {cs = (k₀ , s₀) :: cs'} {ds} {k} {s}
  ( (t₀ , (lkt₀ , r₀)) , rest )
  lk
  with k ≟ k₀
... | no _ =
  Components⊑-lookup rest lk
... | yes refl =
  let s₀≡s = just-inj lk in
  t₀ , ( lkt₀
       , subst (λ x → Schema⊑ Co x t₀) s₀≡s r₀ )
```

---

### 2.2 Component transitivity

Component refinement composes by transporting each old component through the intermediate API and composing schema refinement.

```agda
Components⊑-trans :
    ∀ {cs ds es}
  → Components⊑ cs ds
  → Components⊑ ds es
  → Components⊑ cs es

Components⊑-trans {cs = []} _ _ = tt

Components⊑-trans
  {cs = (k , s₀) :: cs'} {ds} {es}
  ( (s₁ , (lk₁ , r₀₁)) , rest₀₁ )
  ds⊑es
  =
  ( s₂ , (lk₂ , ⊑Co-trans r₀₁ r₁₂) )
  , Components⊑-trans rest₀₁ ds⊑es
  where
    pushed :
      Σ Schema (λ t →
           lookupComponent k es ≡ just t
         × Schema⊑ Co s₁ t)

    pushed = Components⊑-lookup ds⊑es lk₁

    s₂  = fst pushed
    lk₂ = fst (snd pushed)
    r₁₂ = snd (snd pushed)
```

---

### 2.3 Transporting endpoint lookup

If an endpoint is preserved from `es` to `fs`, and we can look it up in `es`, then it can also be looked up in `fs`, with a refining endpoint.

```agda
Endpoints⊑-lookup :
    ∀ {es fs r m e}
  → Endpoints⊑ es fs
  → lookupEndpoint r m es ≡ just e
  → Σ Endpoint (λ e' →
       lookupEndpoint r m fs ≡ just e'
     × Endpoint⊑ e e')

Endpoints⊑-lookup {es = []} _ ()

Endpoints⊑-lookup
  {es = h :: es'} {fs} {r} {m} {e}
  ( (e₀ , (lk₀ , r₀)) , rest )
  lk
  with Path≟ r (Endpoint.route h)
... | no _ =
  Endpoints⊑-lookup rest lk
... | yes refl
  with Method≟ m (Endpoint.method h)
...   | no _ =
        Endpoints⊑-lookup rest lk
...   | yes refl =
        let h≡e = just-inj lk in
        e₀ , ( lk₀
             , subst (λ x → Endpoint⊑ x e₀) h≡e r₀ )
```

---

### 2.4 Endpoint transitivity

Endpoint refinement over lists composes in the same way: each old endpoint is transported through the intermediate API and its refinement witnesses are composed using `Endpoint⊑-trans`.

```agda
Endpoints⊑-trans :
    ∀ {es fs gs}
  → Endpoints⊑ es fs
  → Endpoints⊑ fs gs
  → Endpoints⊑ es gs

Endpoints⊑-trans {es = []} _ _ = tt

Endpoints⊑-trans
  {es = e :: es'} {fs} {gs}
  ( (e₁ , (lk₁ , r₀₁)) , rest₀₁ )
  fs⊑gs
  =
  ( e₂ , (lk₂ , Endpoint⊑-trans r₀₁ r₁₂) )
  , Endpoints⊑-trans rest₀₁ fs⊑gs
  where
    pushed :
      Σ Endpoint (λ e' →
           lookupEndpoint
             (Endpoint.route e)
             (Endpoint.method e)
             gs ≡ just e'
         × Endpoint⊑ e₁ e')

    pushed =
      Endpoints⊑-lookup
        fs⊑gs
        lk₁

    e₂  = fst pushed
    lk₂ = fst (snd pushed)
    r₁₂ = snd (snd pushed)
```

---

### 2.5 API transitivity

Finally, API refinement composes when both component refinement and endpoint refinement compose.

```agda
API⊑-trans :
  ∀ {a₀ a₁ a₂}
  → API⊑ a₀ a₁
  → API⊑ a₁ a₂
  → API⊑ a₀ a₂

API⊑-trans
  (⊑-api wf₀ wf₁ comps₀₁ paths₀₁)
  (⊑-api _   wf₂ comps₁₂ paths₁₂)
  =
  ⊑-api
    wf₀
    wf₂
    (Components⊑-trans comps₀₁ comps₁₂)
    (Endpoints⊑-trans  paths₀₁ paths₁₂)
```

---

## 3. API refinement as a preorder

We now package API refinement as a preorder over well-formed APIs.

```agda
WFAPIₛ : Set
WFAPIₛ = Σ API WFAPI

_⊑APIWF_ : WFAPIₛ → WFAPIₛ → Set
(a , _) ⊑APIWF (b , _) = API⊑ a b
```

Reflexivity and transitivity follow directly from the previously established lemmas.

```agda
API⊑-preorder : IsPreorder _⊑APIWF_
API⊑-preorder = record
  { reflexive  =
      λ { {x = (a , wf)} →
          API⊑-refl wf }

  ; transitive =
      λ { {x = (a₀ , _)}
           {y = (a₁ , _)}
           {z = (a₂ , _)}
           r₀₁ r₁₂ →
          API⊑-trans r₀₁ r₁₂ }
  }
```
