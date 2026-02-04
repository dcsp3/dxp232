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

---

We prove this by structural recursion on the well-formedness derivation. The primitive
and array cases are straightforward. The object case requires a small helper lemma
showing that each property can be looked up in its own property list, allowing us to
build the `PropsRefine` witness.


### 1.1 Lookup helpers

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

---

layman terms explanation (incorporate this later maybe):
We need to prove `PropsRefine Schema⊑Co props props`

But `PropsRefine` is defined by lookup into the new list. So even reflexivity needs a witness that says:
- each key in props can be looked up in props
- and its schema refines itself

that’s what `PropsRefine-refl` gives us...

```
-- if ps already refines the target object, then adding a new field (k,s) to the target is safe as long as k is fresh
-- old properties are still preserved, matching OpenAPI’s backward-compatibility rule for responses

PropsRefine-insert-after-head :
    ∀ {k0 s0 k s ps target}
  → PropsRefine Schema⊑Co ps ((k0 , s0) :: target)
  → k ∉ keys ps
  → PropsRefine Schema⊑Co ps ((k0 , s0) :: (k , s) :: target)

PropsRefine-insert-after-head {ps = []} tt _ = tt

PropsRefine-insert-after-head
  {k0 = k0} {s0 = s0} {k = k} {s = s}
  {ps = (x , sx) :: ps'} {target = target}
  ((sn , (eq , ref)) , rest)
  (notin::_ k≢x k∉tail)
  =
  ( sn
  , ( eq' , ref )
  )
  , PropsRefine-insert-after-head
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
```

```agda
-- adding a fresh property k preserves refinement of existing properties, provided it doesn't already exist

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
  , PropsRefine-insert-after-head
    {k0 = k} {s0 = sch} {k = k'} {s = sch'} {ps = ps'} {target = ps'}
    (PropsRefine-tail {k = k} {sch = sch} {ps = ps'} wfSch uniqTail k∉tail rest)
    k'∉tail                                    -- Proof that k' is not in ps'
```

```agda
-- property refinement reflexivity final boss ie what we use in the main lemmas
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
  -- primitives refine themselves (same primitive type)
  ⊑-prim
    (wf-prim prim items≡ props≡ req≡)
    (wf-prim prim items≡ props≡ req≡)
    prim prim refl

⊑Co-refl (wf-array ty≡ items≡ wfItem props≡ req≡) =
  ⊑-array
    -- arrays refine covariantly when their item schemas refine (recurse on items)
    (wf-array ty≡ items≡ wfItem props≡ req≡)
    (wf-array ty≡ items≡ wfItem props≡ req≡)
    ty≡ ty≡
    items≡ items≡
    (⊑Co-refl wfItem)

⊑Co-refl (wf-object ty≡ items≡ wfProps wfReq wfUniq reqUniq) =
  ⊑-object
    -- objects refine when all old properties are preserved and refine
    (wf-object ty≡ items≡ wfProps wfReq wfUniq reqUniq)
    (wf-object ty≡ items≡ wfProps wfReq wfUniq reqUniq)
    ty≡ ty≡
    (PropsRefine-refl wfUniq wfProps)
    ⊆-refl
```

---

## 2. Transitivity

The refinement relation `Schema⊑Co` is intended to model safe evolution of schemas. Reflexivity already tells us that “no change” is always safe. The next structural property we need is transitivity:

>If `s` safely refines `t`, and `t` safely refines `u`, then `s` safely refines `u`.

This allows us to compress those step-by-step witnesses into a single compatibility guarantee for the whole change.

We prove transitivity by structural recursion on the refinement witness.

- For primitive schemas, transitivity reduces to transitivity of the underlying type equality.
- For arrays, it reduces to transitivity of refinement on the item schema.
- For objects, we must compose both field-wise refinement and the condition on required fields.

Only the object case needs helper lemmas. Object refinement consists of a `PropsRefine Schema⊑Co` witness, ensuring every old field exists in the new object with a refining schema, together with a subset condition `required old ⊆ required new`, ensuring required keys may only grow.

To compose object refinement, we therefore need transitivity of subset witnesses (`⊆-trans`) and a lemma that composes `PropsRefine` witnesses by transporting lookups across an intermediate property list.

With these helpers in place, the main transitivity proof follows by direct structural recursion.

---

### 2.1 Transporting lookups across property refinement

To compose object refinement witnesses, we must reason about individual fields.

If a list of properties `ps` refines into `qs`, then every property appearing in `ps` must also appear in `qs` with a refining schema.
In particular, if looking up a key `k` in `ps` succeeds, then looking up the same key in `qs` must also succeed, and the corresponding schemas must be related by `Schema⊑Co`.

```agda
just-inj : ∀ {A : Set} {x y : A} → just x ≡ just y → x ≡ y
just-inj refl = refl

-- If ps refines qs, then any successful lookup in ps
-- corresponds to a successful lookup in qs, with a refinement witness.
PropsRefine-respects-lookup :
    ∀ {k s ps qs}
  → PropsRefine Schema⊑Co ps qs
  → lookupProp k ps ≡ just s
  → ∃ (λ t → (lookupProp k qs ≡ just t) × (Schema⊑Co s t))

-- ps = []: lookupProp k [] = nothing, so it can't be just s.
PropsRefine-respects-lookup {ps = []} tt ()

-- ps = (k0 , s0) :: ps'
PropsRefine-respects-lookup
  {k = k} {s = s} {ps = (k0 , s0) :: ps'} {qs = qs}
  ((t0 , (lkHead , refHead)) , refTail)
  lk
  with k ≟ k0

... | yes k≡k0 = result
  where
    -- In this branch, the lookup key matches the head key.
    -- So lookupProp k ps returning just s really means the head schema is s.
    s0≡s : s0 ≡ s
    s0≡s = just-inj lk

    -- lkHead talks about key k0; rewrite it to key k using k≡k0.
    lkHead' : lookupProp k qs ≡ just t0
    lkHead' = subst (λ x → lookupProp x qs ≡ just t0) (sym k≡k0) lkHead

    -- refHead is for s0; rewrite it to be for s using s0≡s.
    refHead' : Schema⊑Co s t0
    refHead' = subst (λ x → Schema⊑Co x t0) s0≡s refHead

    -- Return the matching schema t0 from qs, plus the two facts we just built.
    result : ∃ (λ t → (lookupProp k qs ≡ just t) × (Schema⊑Co s t))
    result = (t0 , (lkHead' , refHead'))

... | no k≢k0 =
  -- Keys differ, so lookupProp skips the head.
  -- Agda has already reduced lk to a tail-lookup fact, so we can recurse directly.
  PropsRefine-respects-lookup
    {k = k} {s = s} {ps = ps'} {qs = qs}
    refTail
    lk
```

### 2.2
