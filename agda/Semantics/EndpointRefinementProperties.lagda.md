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

### 1.2 Body

```agda

```

---

### 1.3 Responses
