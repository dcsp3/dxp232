# Schema Refinement Properties

This module contains the core metatheory for covariant schema refinement. In particular,
we show that `Schema⊑Co` forms a **preorder**:

- **reflexive**: every well-formed schema refines itself
- **transitive**: refinements compose

These properties are essential for reasoning about multi-step API evolution and later
support the soundness argument for an operational evolution calculus.

---

```agda
module Semantics.SchemaRefinementProperties where

open import Prelude
open import Syntax
open import WellFormed.Core

open import Semantics.SchemaRefinement
```

## 1. Reflexivity

Reflexivity states that every well-formed schema is a safe replacement for itself.

```agda
-- todo: cleanup code and explanations
⊑Co-refl : ∀ {s} → WFSchema s → Schema⊑Co s s
```

We prove this by structural recursion on the well-formedness derivation. The primitive
and array cases are straightforward. The object case requires a small helper lemma
showing that each property can be looked up in its own property list, allowing us to
build the `PropsRefine` witness.


### 1.1 Lookup helpers
git
The object case relies on the fact that looking up a key at the head of an association list succeeds.

```agda

-- If the key we’re looking for is at the head of the list, lookup returns that schema.
lookupProp-here :
    ∀ {k s ps}
  → lookupProp k ((k , s) :: ps) ≡ just s
lookupProp-here {k} {s} {ps} with k ≟ k
... | yes _   = refl
... | no  nk  = ⊥-elim (nk refl)


-- If the head key is different, looking up k in (k' , s) :: ps is the same as looking up k in ps.
lookupProp-skip :
    ∀ {k k' s ps}
  → k ≢ k'
  → lookupProp k ((k' , s) :: ps) ≡ lookupProp k ps
lookupProp-skip {k} {k'} {s} {ps} k≢k' with k ≟ k'
... | yes eq = ⊥-elim (k≢k' eq)
... | no  _  = refl

-- Inserting a pair (k,s) after the head doesn’t affect lookup for any key x as long as x ≢ k.
lookupProp-insert-after-head :
    ∀ {x k0 s0 k s target}
  → x ≢ k
  → lookupProp x ((k0 , s0) :: (k , s) :: target)
    ≡ lookupProp x ((k0 , s0) :: target)
lookupProp-insert-after-head {x} {k0} {s0} {k} {s} {target} x≢k with x ≟ k0
... | yes _ = refl
... | no  _ = lookupProp-skip {k = x} {k' = k} {s = s} {ps = target} x≢k
```

### 1.2 Reflexivity for property refinement

To construct the object refinement witness in the reflexivity proof, we show that a
property list refines itself (field-by-field) under `Schema⊑Co`.

This relies on the well-formedness invariant that object property keys are unique so that the list behaves like a real property map; otherwise refinement becomes order-sensitive and can misrepresent OpenAPI objects.

```

skip-after-head :
    ∀ {k0 s0 k s ps target}
  → PropsRefine Schema⊑Co ps ((k0 , s0) :: target)
  → k ∉ keys ps
  → PropsRefine Schema⊑Co ps ((k0 , s0) :: (k , s) :: target)

skip-after-head {ps = []} tt _ = tt

skip-after-head
  {k0 = k0} {s0 = s0} {k = k} {s = s}
  {ps = (x , sx) :: ps'} {target = target}
  ((sn , (eq , ref)) , rest)
  (notin::_ k≢x k∉tail)
  =
  ( sn
  , ( eq' , ref )
  )
  , skip-after-head
    {k0 = k0} {s0 = s0} {k = k} {s = s} {ps = ps'} {target = target}
    rest
    k∉tail
  where
    -- we need x ≢ k, but notin gives k ≢ x
    x≢k : x ≢ k
    x≢k e = k≢x (sym e)

    eq' : lookupProp x ((k0 , s0) :: (k , s) :: target) ≡ just sn
    eq' =
      trans
        (lookupProp-insert-after-head x≢k)
        eq

-- Tail-to-whole: if k is not in keys ps, then ps refines (k,sch)::ps.
PropsRefine-tail :
    ∀ {k sch ps}
  → WFSchema sch
  → Unique (keys ps)
  → k ∉ keys ps
  → All (λ { (_ , s) → WFSchema s }) ps
  → PropsRefine Schema⊑Co ps ((k , sch) :: ps)

PropsRefine-tail wfSch uniq notin[] all[] = tt

PropsRefine-tail {k} {sch} {ps = (k' , sch') :: ps'}
  wfSch
  (uniq::_ k'∉tail uniqTail) -- Deconstruct uniqueness
  (notin::_ k≢k' k∉tail)
  (all::_ wfSch' rest)
  = 
  -- 1. Head witness: (k', sch') is in ((k, sch) :: (k', sch') :: ps')
  (sch' , (trans (lookupProp-skip (λ e → k≢k' (sym e))) lookupProp-here , ⊑Co-refl wfSch'))
  
  -- 2. Tail witness: use skip-after-head to insert (k', sch') into the target of the recursion
  , skip-after-head
    {k0 = k} {s0 = sch} {k = k'} {s = sch'} {ps = ps'} {target = ps'}
    (PropsRefine-tail {k = k} {sch = sch} {ps = ps'} wfSch uniqTail k∉tail rest)
    k'∉tail                                    -- Proof that k' is not in ps'

PropsRefine-refl :
    ∀ {ps}
  → Unique (keys ps)
  → All (λ { (_ , s) → WFSchema s }) ps
  → PropsRefine Schema⊑Co ps ps
PropsRefine-refl {ps = []} uniq all = tt

PropsRefine-refl {ps = (k , sch) :: ps'}
  (uniq::_ k∉tail uniqTail)
  (all::_ wfSch rest)
  =
  ( sch
  , ( lookupProp-here {k = k} {s = sch} {ps = ps'}
    , ⊑Co-refl wfSch
    )
  )
  , PropsRefine-tail
      {k = k} {sch = sch} {ps = ps'}
      wfSch
      uniqTail
      k∉tail
      rest
```

### 1.3 Main Reflexivity Lemma

```agda
⊑Co-refl (wf-prim prim items≡ props≡ req≡) =
  ⊑-prim
    (wf-prim prim items≡ props≡ req≡)
    (wf-prim prim items≡ props≡ req≡)
    prim prim refl

⊑Co-refl (wf-array ty≡ items≡ wfItem props≡ req≡) =
  ⊑-array
    (wf-array ty≡ items≡ wfItem props≡ req≡)
    (wf-array ty≡ items≡ wfItem props≡ req≡)
    ty≡ ty≡
    items≡ items≡
    (⊑Co-refl wfItem)

⊑Co-refl (wf-object ty≡ items≡ wfProps wfReq wfUniq) =
  ⊑-object
    (wf-object ty≡ items≡ wfProps wfReq wfUniq)
    (wf-object ty≡ items≡ wfProps wfReq wfUniq)
    ty≡ ty≡
    (PropsRefine-refl wfUniq wfProps)
```

---

