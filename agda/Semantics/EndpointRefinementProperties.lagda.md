# Endpoint Refinement Properties

Endpoint refinement captures when one endpoint can safely replace another.
Having defined the relation itself, we now establish its basic algebraic structure.

In particular, we show that `Endpoint⊑` is a **preorder**:

- it relates every endpoint to itself
- and compatible evolutions compose

These results justify treating endpoint refinement as a principled notion
of safe API evolution.

```agda
module Semantics.EndpointRefinementProperties where

open import Prelude
open import Syntax
open import WellFormed.Core

open import Semantics.Variance
open import Semantics.SchemaRefinement
open import Semantics.SchemaRefinementProperties

open import Semantics.EndpointRefinement

open Σ using (fst ; snd)
```

---

## 1. Reflexivity

Every well-formed endpoint safely refines itself.

We prove this by establishing reflexivity for each component, then combining them.

### 1.1 Parameter reflexivity

Parameter refinement is defined structurally over lists, so reflexivity is obtained by simple recursion.

```agda
Params⊑Contra-weaken :
    ∀ {h ps new}
  → paramKey h ∉ paramKeys ps
  → Params⊑Contra ps new
  → Params⊑Contra ps (h :: new)
Params⊑Contra-weaken {ps = []} _ tt = tt
Params⊑Contra-weaken {h} {ps = q :: qs} {new}
  (notin::_ h≢q h∉qs)
  ( (q' , (lkq' , rq')) , rest )
  =
  ( q'
  , ( lookupParam-there h≢q lkq'
    , rq'
    )
  )
  , Params⊑Contra-weaken h∉qs rest

Param⊑Contra-refl : ∀ p → Param⊑Contra p p
Param⊑Contra-refl _ = (refl , (refl , (refl , (λ x → x))))

Params⊑Contra-refl :
    ∀ {ps}
  → Unique (paramKeys ps)
  → Params⊑Contra ps ps
Params⊑Contra-refl {ps = []} uniq[] = tt
Params⊑Contra-refl {ps = p :: ps} (uniq::_ p∉tail uniqTail) =
  ( p , (lookupParam-here , Param⊑Contra-refl p) )
  , Params⊑Contra-weaken p∉tail (Params⊑Contra-refl uniqTail)
```

---

### 1.2 Body reflexivity

Body refinement is contravariant, but reflexivity follows directly from
reflexivity of schema refinement.

```agda
Body⊑Contra-refl :
    ∀ {m} {b : Body m}
  → WFBody b
  → Body⊑Contra refl b b
Body⊑Contra-refl wf-nobody         = tt
Body⊑Contra-refl wf-nobodyD        = tt
Body⊑Contra-refl (wf-hasBody  wfS) = ⊑Co-refl wfS
Body⊑Contra-refl (wf-hasBodyU wfS) = ⊑Co-refl wfS
Body⊑Contra-refl (wf-hasBodyP wfS) = ⊑Co-refl wfS
```

---

### 1.3 Response reflexivity

Responses are checked covariantly. Reflexivity follows by recursion, using a weakening lemma to show that adding a fresh head response does not affect lookups for the tail statuses.

```agda
Resps⊑Co-weaken :
    ∀ {st₀ s₀ rs new}
  → st₀ ∉ respKeys rs
  → Resps⊑Co rs new
  → Resps⊑Co rs (response st₀ s₀ :: new)
Resps⊑Co-weaken {rs = []} _ tt = tt
Resps⊑Co-weaken {st₀} {s₀} {rs = response st s :: rs} {new}
  (notin::_ st₀≢st st₀∉tail)
  ( (t , (lkt , rt)) , rest )
  =
  ( t
  , ( lookupResp-there st₀≢st lkt
    , rt
    )
  )
  , Resps⊑Co-weaken st₀∉tail rest

Resps⊑Co-refl :
    ∀ {rs}
  → Unique (respKeys rs)
  → All WFResponse rs
  → Resps⊑Co rs rs
Resps⊑Co-refl {rs = []} uniq[] all[] = tt
Resps⊑Co-refl {rs = response st s :: rs}
  (uniq::_ st∉tail uniqTail)
  (all::_ (wf-response wfS) rest)
  =
  ( s
  , ( lookupResp-here {st = st} {s = s} {rs = rs}
    , ⊑Co-refl wfS
    )
  )
  , Resps⊑Co-weaken st∉tail (Resps⊑Co-refl uniqTail rest)
```

### 1.4 Endpoint reflexivity

Finally, reflexivity of `Endpoint⊑` follows by combining the component
reflexivity lemmas.

```agda
Endpoint⊑-refl :
    ∀ {e}
  → WFEndpoint e
  → Endpoint⊑ e e
Endpoint⊑-refl {e} wf@(wf-endpoint _ _ uniqParams wfBody wfResps uniqResps) =
  ⊑-endpoint
    wf
    wf
    refl
    refl
    (Params⊑Contra-refl uniqParams)
    (Body⊑Contra-refl wfBody)
    (Resps⊑Co-refl uniqResps wfResps)
```

---

## 2. Transitivity

If `e₀` refines to `e₁` and `e₁` refines to `e₂`, then `e₀` refines to `e₂`.

As in reflexivity, we prove this component-wise and then combine the results.

### 2.1 Parameter transitivity

At the level of a single parameter, transitivity is immediate: all fields are
checked by equality (or weakening of required), and equality composes.

```agda
ReqWeakens-trans :
    ∀ {a b c}
  → ReqWeakens a b
  → ReqWeakens b c
  → ReqWeakens a c
ReqWeakens-trans a≤b b≤c c≡true =
  a≤b (b≤c c≡true)

Param⊑Contra-trans :
    ∀ {p q r}
  → Param⊑Contra p q
  → Param⊑Contra q r
  → Param⊑Contra p r
Param⊑Contra-trans
  (loc≡₁ , (name≡₁ , (sch≡₁ , req≤₁)))
  (loc≡₂ , (name≡₂ , (sch≡₂ , req≤₂)))
  =
  ( trans loc≡₁ loc≡₂
  , ( trans name≡₁ name≡₂
    , ( trans sch≡₁ sch≡₂
      , ReqWeakens-trans req≤₁ req≤₂
      )
    )
  )
```

### 2.2 Parameter list transitivity

`Params⊑Contra` is defined by iterating over the old list and using lookup to
align each old parameter with a corresponding new one. To compose two such
proofs, we need one small helper: if a parameter can be looked up in the
intermediate list, then the refinement proof for that intermediate list tells
us how it maps forward.

```agda
Params⊑Contra-lookup :
    ∀ {qs rs ℓ k q}
  → Params⊑Contra qs rs
  → lookupParam ℓ k qs ≡ just q
  → Σ Parameter (λ r →
       lookupParam ℓ k rs ≡ just r
     × Param⊑Contra q r)
Params⊑Contra-lookup {qs = []} tt ()
Params⊑Contra-lookup {qs = q₀ :: qs} {rs} {ℓ} {k} {q}
  ( (r₀ , (lkr₀ , q₀⊑r₀)) , rest )
  lk
  with ParamLocation≟ ℓ (Parameter.location q₀)
... | no _ =
  Params⊑Contra-lookup rest lk
... | yes refl
  with (k ≟ Parameter.name q₀)
... | no _ =
  Params⊑Contra-lookup rest lk
... | yes refl =
  let q₀≡q : q₀ ≡ q
      q₀≡q = just-inj lk
  in
  r₀
  , ( lkr₀
    , subst (λ x → Param⊑Contra x r₀) q₀≡q q₀⊑r₀
    )

Params⊑Contra-trans :
    ∀ {ps qs rs}
  → Params⊑Contra ps qs
  → Params⊑Contra qs rs
  → Params⊑Contra ps rs
Params⊑Contra-trans {ps = []} _ _ = tt
Params⊑Contra-trans {ps = p :: ps} {qs} {rs}
  ( (q , (lkq , p⊑q)) , ps⊑qs )
  qs⊑rs
  =
  ( r
  , ( lkr
    , Param⊑Contra-trans p⊑q q⊑r
    )
  )
  , Params⊑Contra-trans ps⊑qs qs⊑rs
  where
    r-wit :
      Σ Parameter (λ r →
           lookupParam (Parameter.location p) (Parameter.name p) rs ≡ just r
         × Param⊑Contra q r)
    r-wit = Params⊑Contra-lookup qs⊑rs lkq

    r   : Parameter
    r   = fst r-wit

    lkr : lookupParam (Parameter.location p) (Parameter.name p) rs ≡ just r
    lkr = fst (snd r-wit)

    q⊑r : Param⊑Contra q r
    q⊑r = snd (snd r-wit)
```
