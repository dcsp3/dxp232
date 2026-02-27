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
open import Syntax.Syntax
open import Syntax.Decidable

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

---

### 1.1 Parameter reflexivity

Parameter refinement is defined structurally over lists, so reflexivity is obtained by simple recursion.

```agda
OldParamsPreserved-weaken :
    ∀ {h ps new}
  → paramKey h ∉ paramKeys ps
  → OldParamsPreserved ps new
  → OldParamsPreserved ps (h :: new)

OldParamsPreserved-weaken {ps = []} _ tt = tt

OldParamsPreserved-weaken
  {h} {ps = q :: qs} {new}
  (notin::_ h≢q h∉qs)
  ( (q' , (lkq' , rq')) , rest )
  =
  ( q'
  , ( lookupParam-there h≢q lkq'
    , rq'
    )
  )
  , OldParamsPreserved-weaken h∉qs rest
  ```

```agda
Param⊑Contra-refl : ∀ p → Param⊑Contra p p
Param⊑Contra-refl _ = (refl , (refl , (refl , (λ x → x))))
```

```agda
Params⊑Contra-refl :
  ∀ {ps}
  → Unique (paramKeys ps)
  → Params⊑Contra ps ps

Params⊑Contra-refl {ps = []} uniq[] =
  ( tt
  , λ lk reqTrue →
      _ , (lk , reqTrue)
  )

Params⊑Contra-refl {ps = p :: ps}
  (uniq::_ p∉tail uniqTail)
  =
  ( ( p , (lookupParam-here , Param⊑Contra-refl p) )
    , OldParamsPreserved-weaken p∉tail (fst rec)
  )
  ,
  ( λ lk reqTrue →
      _ , (lk , reqTrue)
  )
  where
    rec = Params⊑Contra-refl uniqTail
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

---

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

---

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

---

### 2.2 Parameter list transitivity

`Params⊑Contra` is defined by iterating over the old list and using lookup to
align each old parameter with a corresponding new one. To compose two such
proofs, we need one small helper: if a parameter can be looked up in the
intermediate list, then the refinement proof for that intermediate list tells
us how it maps forward.

```agda
OldParamsPreserved-lookup :
  ∀ {qs rs ℓ k q}
  → OldParamsPreserved qs rs
  → lookupParam ℓ k qs ≡ just q
  → Σ Parameter (λ r →
       lookupParam ℓ k rs ≡ just r
     × Param⊑Contra q r)

OldParamsPreserved-lookup {qs = []} _ ()

OldParamsPreserved-lookup
  {qs = q₀ :: qs} {rs} {ℓ} {k} {q}
  ( (r₀ , (lkr₀ , q₀⊑r₀)) , rest )
  lk
  with ParamLocation≟ ℓ (Parameter.location q₀)
... | no _ = OldParamsPreserved-lookup rest lk
... | yes refl
  with (k ≟ Parameter.name q₀)
... | no _ = OldParamsPreserved-lookup rest lk
... | yes refl =
  let q₀≡q = just-inj lk in
  r₀ , (lkr₀ , subst (λ x → Param⊑Contra x r₀) q₀≡q q₀⊑r₀)
```

```agda
OldParamsPreserved-trans :
  ∀ {ps qs rs}
  → OldParamsPreserved ps qs
  → OldParamsPreserved qs rs
  → OldParamsPreserved ps rs

OldParamsPreserved-trans {ps = []} _ _ = tt

OldParamsPreserved-trans {ps = p :: ps}
  ( (q , (lkq , p⊑q)) , ps≤qs )
  qs≤rs
  =
  ( r
  , ( lkr
    , Param⊑Contra-trans p⊑q q⊑r
    )
  )
  , OldParamsPreserved-trans ps≤qs qs≤rs
  where
    r-wit =
      OldParamsPreserved-lookup qs≤rs lkq

    r   = fst r-wit
    lkr = fst (snd r-wit)
    q⊑r = snd (snd r-wit)
```

```agda
NewRequiredSafe-trans :
  ∀ {ps qs rs}
  → NewRequiredSafe ps qs
  → NewRequiredSafe qs rs
  → NewRequiredSafe ps rs
  
NewRequiredSafe-trans {ps} {qs} {rs}
  ps≤qs qs≤rs {ℓ} {k} {p} lk reqTrue =
  let (q , (lkq , reqq)) = qs≤rs {ℓ} {k} {p} lk reqTrue
      (p' , (lkp , reqp)) = ps≤qs {ℓ} {k} {q} lkq reqq
  in (p' , (lkp , reqp))
```

```agda
Params⊑Contra-trans :
  ∀ {ps qs rs}
  → Params⊑Contra ps qs
  → Params⊑Contra qs rs
  → Params⊑Contra ps rs

Params⊑Contra-trans {ps} {qs} {rs}
  (psOld , psReq)
  (qsOld , qsReq)
  =
  ( OldParamsPreserved-trans psOld qsOld
  , NewRequiredSafe-trans {ps} {qs} {rs} psReq qsReq
  )
```

---

### 2.3 Body transitivity

Body refinement composes by composition of schema refinement.

```agda
Body⊑Contra-trans :
  ∀ {m₀ m₁ m₂}
    {b₀ : Body m₀}
    {b₁ : Body m₁}
    {b₂ : Body m₂}
  → (eq₀₁ : m₀ ≡ m₁)
  → (eq₁₂ : m₁ ≡ m₂)
  → Body⊑Contra eq₀₁ b₀ b₁
  → Body⊑Contra eq₁₂ b₁ b₂
  → Body⊑Contra (trans eq₀₁ eq₁₂) b₀ b₂
  
Body⊑Contra-trans
  {b₀ = b₀}
  {b₁ = b₁}
  {b₂ = b₂}
  refl refl p q
  with b₀ | b₁ | b₂
... | NoBody   | NoBody   | NoBody   = tt
... | NoBodyD  | NoBodyD  | NoBodyD  = tt
... | HasBody s₀  | HasBody s₁  | HasBody s₂  =
      ⊑Co-trans q p
... | HasBodyU s₀ | HasBodyU s₁ | HasBodyU s₂ =
      ⊑Co-trans q p
... | HasBodyP s₀ | HasBodyP s₁ | HasBodyP s₂ =
      ⊑Co-trans q p
```

---

### 2.4 Response transitivity

```agda
Resps⊑Co-lookup :
    ∀ {rs ss st s}
  → Resps⊑Co rs ss
  → lookupResp st rs ≡ just s
  → Σ Schema (λ t →
       lookupResp st ss ≡ just t
     × Schema⊑ Co s t)

Resps⊑Co-lookup {rs = []} _ ()
Resps⊑Co-lookup {rs = response st₀ s₀ :: rs}
                 {ss} {st} {s}
                 ( (t₀ , (lkt₀ , s₀⊑t₀)) , rest )
                 lk
  with Status≟ st st₀
... | no _ =
  Resps⊑Co-lookup rest lk
... | yes refl =
  let s₀≡s : s₀ ≡ s
      s₀≡s = just-inj lk
  in
  t₀
  , ( lkt₀
    , subst (λ x → Schema⊑ Co x t₀) s₀≡s s₀⊑t₀
    )

Resps⊑Co-trans :
    ∀ {rs ss ts}
  → Resps⊑Co rs ss
  → Resps⊑Co ss ts
  → Resps⊑Co rs ts

Resps⊑Co-trans {rs = []} _ _ = tt

Resps⊑Co-trans {rs = response st s :: rs}
               {ss} {ts}
               ( (t , (lkt , s⊑t)) , rs⊑ss )
               ss⊑ts
  =
  ( u
  , ( lku
    , ⊑Co-trans s⊑t t⊑u
    )
  )
  , Resps⊑Co-trans rs⊑ss ss⊑ts
  where

    u-wit :
      Σ Schema (λ u →
           lookupResp st ts ≡ just u
         × Schema⊑ Co t u)

    u-wit = Resps⊑Co-lookup ss⊑ts lkt

    u : Schema
    u = fst u-wit

    lku : lookupResp st ts ≡ just u
    lku = fst (snd u-wit)

    t⊑u : Schema⊑ Co t u
    t⊑u = snd (snd u-wit)
```

---

### 2.5 Endpoint transitivity

Endpoint refinement composes across endpoints: if e₀ ⊑ e₁ and e₁ ⊑ e₂, then e₀ ⊑ e₂.

```agda
Endpoint⊑-trans :
  ∀ {e₀ e₁ e₂}
  → Endpoint⊑ e₀ e₁
  → Endpoint⊑ e₁ e₂
  → Endpoint⊑ e₀ e₂

Endpoint⊑-trans
  (⊑-endpoint wf₀ wf₁ routeEq₀ methodEq₀
               params₀⊑₁ body₀⊑₁ resps₀⊑₁)
  (⊑-endpoint _   wf₂ routeEq₁ methodEq₁
               params₁⊑₂ body₁⊑₂ resps₁⊑₂)
  =
  ⊑-endpoint
    wf₀
    wf₂
    (trans routeEq₀ routeEq₁)
    (trans methodEq₀ methodEq₁)
    (Params⊑Contra-trans params₀⊑₁ params₁⊑₂)
    (Body⊑Contra-trans methodEq₀ methodEq₁ body₀⊑₁ body₁⊑₂)
    (Resps⊑Co-trans resps₀⊑₁ resps₁⊑₂)
```

---

## 3. Endpoint refinement as a preorder

Reflexivity of `Endpoint⊑` requires a well-formedness proof.
So, as with schemas, we define the preorder over endpoints paired with their `WFEndpoint` witness.

```agda
-- an endpoint packaged together with a proof that it is well-formed
WFEndpointₛ : Set
WFEndpointₛ = Σ Endpoint WFEndpoint

-- lift Endpoint⊑ to well-formed endpoints
_⊑EndpointWF_ : WFEndpointₛ → WFEndpointₛ → Set
(e , _) ⊑EndpointWF (e' , _) = Endpoint⊑ e e'


Endpoint⊑-preorder : IsPreorder _⊑EndpointWF_
Endpoint⊑-preorder = record
  { reflexive  =
      λ { {x = (e , wf)} →
          Endpoint⊑-refl wf }

  ; transitive =
      λ { {x = (e₀ , _)}
           {y = (e₁ , _)}
           {z = (e₂ , _)}
           e₀⊑e₁ e₁⊑e₂ →
           Endpoint⊑-trans e₀⊑e₁ e₁⊑e₂ }
  }
```
