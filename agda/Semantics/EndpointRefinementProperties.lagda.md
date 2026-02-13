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
Body⊑Contra-refl wf-nobody   = tt
Body⊑Contra-refl wf-nobodyD  = tt
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
Endpoint⊑-refl {e} (wf-endpoint wfPath wfParams uniqParams wfBody wfResps uniqResps) =
  ⊑-endpoint
    (wf-endpoint wfPath wfParams uniqParams wfBody wfResps uniqResps)
    (wf-endpoint wfPath wfParams uniqParams wfBody wfResps uniqResps)
    refl
    refl
    (Params⊑Contra-refl uniqParams)
    (Body⊑Contra-refl wfBody)
    (Resps⊑Co-refl uniqResps wfResps)
```

---

## 2. Transitivity
