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
open import Syntax.Syntax
open import WellFormed.Core

open import Semantics.SchemaRefinement

open Σ using (fst ; snd)
```

## 1. Reflexivity

Reflexivity states that every well-formed schema is a safe replacement for itself.

```agda
⊑Co-refl : ∀ {s} → WFSchema s → Schema⊑Co s s
```

We prove this by structural recursion on the well-formedness derivation. The primitive
and array cases are straightforward. The object case requires a small helper lemma
showing that each property can be looked up in its own property list, allowing us to
build the `PropsRefine` witness.

### 1.1 Lookup helpers

The object case relies on the fact that looking up a key at the head of an association list succeeds.

```agda
-- Lookup succeeds when the key is at the head of the list
lookupProp-here :
    ∀ {k s ps}
  → lookupProp k ((k , s) :: ps) ≡ just s
lookupProp-here {k} {s} {ps} with k ≟ k
... | yes _    = refl
... | no  k≢k  = ⊥-elim (k≢k refl)


-- If the head key is different, skip the head (i.e search the tail)
lookupProp-skip :
    ∀ {k k0 s ps}
  → k ≢ k0
  → lookupProp k ((k0 , s) :: ps) ≡ lookupProp k ps
lookupProp-skip {k} {k0} {s} {ps} k≢k0 with k ≟ k0
... | yes k≡k0 = ⊥-elim (k≢k0 k≡k0)
... | no  _    = refl

-- Inserting a fresh pair after the head does not affect lookup for other keys
lookupProp-insert-after-head :
    ∀ {x k0 s0 k s target}
  → x ≢ k
  → lookupProp x ((k0 , s0) :: (k , s) :: target)
    ≡ lookupProp x ((k0 , s0) :: target)
lookupProp-insert-after-head {x} {k0} {s0} {k} {s} {target} x≢k with x ≟ k0
... | yes _ = refl
... | no  _ = lookupProp-skip {k = x} {k0 = k} {s = s} {ps = target} x≢k

-- If a key is absent from the key list, lookup returns nothing
lookupProp-∉-nothing : ∀ {k ps} → k ∉ keys ps → lookupProp k ps ≡ nothing
lookupProp-∉-nothing {k} {[]} _ = refl
lookupProp-∉-nothing {k} {(k' , _) :: ps} (notin::_ k≢k' k∉rest)
  with k ≟ k'
... | yes refl = ⊥-elim (k≢k' refl)
... | no  _    = lookupProp-∉-nothing k∉rest

-- Extract well-formedness from a property lookup
lookupProp-wf : ∀ {k s ps} → All WFSchema (values ps) → lookupProp k ps ≡ just s → WFSchema s
lookupProp-wf {k} {s} {[]} _ ()
lookupProp-wf {k} {s} {(k' , s') :: ps} (all::_ wfS wfRest) lk
  with k ≟ k'
... | yes refl = subst WFSchema (just-inj lk) wfS
... | no  _    = lookupProp-wf wfRest lk
```

---

### 1.2 Reflexivity for property refinement

To construct the object refinement witness in the reflexivity proof, we show that a
property list refines itself (field-by-field) under `Schema⊑Co`.

This relies on the well-formedness invariant that object property keys are unique, so the list behaves like a proper property map. Without uniqueness, refinement would become order-sensitive and could misrepresent OpenAPI objects.

Specifically, we need a a witness that says:
- each key in props can be looked up in props
- and its schema refines itself

and that is what `PropsRefine-refl` gives us.

```
-- If ps refines (k0 , s0) :: target, then inserting a fresh (k , s)
-- after the head preserves refinement of ps
PropsRefine-insert-after-head :
    ∀ {k0 s0 k s ps target}
  → PropsRefine Schema⊑Co ps ((k0 , s0) :: target)
  → k ∉ keys ps
  → PropsRefine Schema⊑Co ps ((k0 , s0) :: (k , s) :: target)

PropsRefine-insert-after-head {ps = []} tt _ = tt

PropsRefine-insert-after-head
  {k0 = k0} {s0 = s0} {k = k} {s = s}
  {ps = (x , sx) :: ps'} {target = target}
  ((sn , (lk , sr)) , tail)
  (notin::_ k≢x k∉tail)
  = (sn , ( eq' , sr ))
  , PropsRefine-insert-after-head
    {k0 = k0} {s0 = s0} {k = k} {s = s} {ps = ps'} {target = target}
    tail
    k∉tail
  where
    x≢k : x ≢ k
    x≢k e = k≢x (sym e)

    eq' : lookupProp x ((k0 , s0) :: (k , s) :: target) ≡ just sn
    eq' =
      trans
        (lookupProp-insert-after-head x≢k)
        lk
```

```agda
-- Adding a fresh property (k , sch) preserves refinement of the existing
-- properties ps into ((k , sch) :: ps)
PropsRefine-tail :
    ∀ {k sch ps}
  → WFSchema sch
  → Unique (keys ps)
  → k ∉ keys ps
  → All WFSchema (values ps)
  → PropsRefine Schema⊑Co ps ((k , sch) :: ps)

PropsRefine-tail {ps = []} wfSch uniq notin all = tt

PropsRefine-tail
  {k} {sch} {ps = (k' , sch') :: ps'}
  wfSch
  (uniq::_ k'∉tail uniqTail)
  (notin::_ k≢k' k∉tail)
  (all::_ wfSch' wfTail)
  =
    (sch' , (lkHead , ⊑Co-refl wfSch'))
  , PropsRefine-insert-after-head
      {k0 = k} {s0 = sch} {k = k'} {s = sch'}
      {ps = ps'} {target = ps'}
      (PropsRefine-tail {k = k} {sch = sch} {ps = ps'} wfSch uniqTail k∉tail wfTail)
      k'∉tail
  where
    -- Lookup k' in ((k , sch) :: (k' , sch') :: ps') succeeds at the second position
    lkHead : lookupProp k' ((k , sch) :: (k' , sch') :: ps') ≡ just sch'
    lkHead = trans (lookupProp-skip (λ e → k≢k' (sym e))) (lookupProp-here {k = k'})
```

```agda
-- A well-formed property list refines itself field-by-field
PropsRefine-refl :
    ∀ {ps}
  → Unique (keys ps)
  → All WFSchema (values ps)
  → PropsRefine Schema⊑Co ps ps
PropsRefine-refl {ps = []} uniq all = tt

PropsRefine-refl
  {ps = (k , sch) :: ps'}
  (uniq::_ k∉tail uniqTail)
  (all::_ wfSch wfTail)
  =
    (sch , (lookupProp-here {k} , ⊑Co-refl wfSch))
  , PropsRefine-tail
      {k = k} {sch = sch} {ps = ps'}
      wfSch uniqTail k∉tail wfTail
```

---

### 1.3 Main Reflexivity Lemma

```agda
⊑Co-refl (wf-prim prim items≡ props≡ req≡) =
  -- Primitives refine themselves (same primitive type)
  ⊑-prim
    (wf-prim prim items≡ props≡ req≡)
    (wf-prim prim items≡ props≡ req≡)
    prim prim refl

⊑Co-refl (wf-array ty≡ items≡ wfItem props≡ req≡) =
  ⊑-array
    -- Arrays refine covariantly when their item schemas refine (recurse on items)
    (wf-array ty≡ items≡ wfItem props≡ req≡)
    (wf-array ty≡ items≡ wfItem props≡ req≡)
    ty≡ ty≡
    items≡ items≡
    (⊑Co-refl wfItem)

⊑Co-refl (wf-object ty≡ items≡ wfProps wfReq wfUniq reqUniq) =
  ⊑-object
    -- Objects refine when all old properties are preserved and refine
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
PropsRefine-respects-lookup :
    ∀ {k s ps qs}
  → PropsRefine Schema⊑Co ps qs
  → lookupProp k ps ≡ just s
  → ∃ (λ t → (lookupProp k qs ≡ just t) × (Schema⊑Co s t))

-- Base case: no fields in ps, so lookup cannot happen
PropsRefine-respects-lookup {ps = []} tt ()

-- Inductive case: compare the lookup key with the head key
PropsRefine-respects-lookup
  {k = k} {s = s} {ps = (k0 , s0) :: ps'} {qs = qs}
  ((t0 , (lkQ , srST)) , tailPQ)
  lk
  with k ≟ k0

... | yes k≡k0 = result
  where
    -- lookup success means head schema is s
    s0≡s : s0 ≡ s
    s0≡s = just-inj lk

    -- rewrite head lookup from k0 to k
    lkQ' : lookupProp k qs ≡ just t0
    lkQ' = subst (λ x → lookupProp x qs ≡ just t0) (sym k≡k0) lkQ

    -- rewrite schema refinement
    srST' : Schema⊑Co s t0
    srST' = subst (λ x → Schema⊑Co x t0) s0≡s srST

    result : ∃ (λ t → (lookupProp k qs ≡ just t) × (Schema⊑Co s t))
    result = (t0 , (lkQ' , srST'))

... | no k≢k0 =
  -- keys differ, skip head and recurse on tail
  PropsRefine-respects-lookup
    {k = k} {s = s} {ps = ps'} {qs = qs}
    tailPQ
    lk
```

---

### 2.2 Transitivity of schema refinement

Transitivity is proved by structural recursion on the first refinement witness. Primitive and array cases are immediate. The object case composes field-wise refinement using `PropsRefine-trans`, and composes the required-key condition using `⊆-trans`.

```agda
⊑Co-trans : ∀ {s t u} → Schema⊑Co s t → Schema⊑Co t u → Schema⊑Co s u
```

### Helper Lemmas

```agda
prim≢array : IsPrimitive array → ⊥
prim≢array ()

prim≢object : IsPrimitive object → ⊥
prim≢object ()

array≢object : array ≡ object → ⊥
array≢object ()
```

### Primitive Cases

```agda
⊑Co-trans
  (⊑-prim wfS wfT primS primT eqST)
  (⊑-prim wfT' wfU primT' primU eqTU)
  =
    ⊑-prim wfS wfU primS primU (trans eqST eqTU)

⊑Co-trans
  (⊑-prim wfS wfT primS primT eqST)
  (⊑-array wfT' wfU tyTArr tyUArr itT itU srTU)
  =
    ⊥-elim (prim≢array (subst IsPrimitive tyTArr primT))

⊑Co-trans
  (⊑-prim wfS wfT primS primT eqST)
  (⊑-object wfT' wfU tyTObj tyUObj prTU reqTU)
  =
    ⊥-elim (prim≢object (subst IsPrimitive tyTObj primT))
```

### Array Cases

```agda
⊑Co-trans
  (⊑-array wfS wfT tySArr tyTArr itemsS itemsT srST)
  (⊑-prim wfT' wfU primT primU eqTU)
  =
    ⊥-elim (prim≢array (subst IsPrimitive tyTArr primT))
  
⊑Co-trans
  (⊑-array wfS wfT tySArr tyTArr itemsS itemsT srST)
  (⊑-object wfT' wfU tyTObj tyUObj prTU reqTU)
  =
    ⊥-elim (array≢object (trans (sym tyTArr) tyTObj))

⊑Co-trans
  (⊑-array {si = si} {ti = ti} wfS wfT tySArr tyTArr itemsS itemsT srST)
  (⊑-array {si = ti'} {ti = ui} wfT' wfU tyTArr' tyUArr itemsT' itemsU srTU)
  = 
    ⊑-array wfS wfU tySArr tyUArr itemsS itemsU srSU    

      where
        -- align the two extracted item schemas from Schema.items t
        ti≡ti' : ti ≡ ti'
        ti≡ti' = just-inj (trans (sym itemsT) itemsT')

        -- rewrite srTU so its domain matches ti
        srTU' : Schema⊑Co ti ui
        srTU' = subst (λ x → Schema⊑Co x ui) (sym ti≡ti') srTU

        -- compose item refinements
        srSU : Schema⊑Co si ui
        srSU = ⊑Co-trans srST srTU'
```

### Object Cases

```agda
⊑Co-trans
  (⊑-object wfS wfT tySObj tyTObj propsST reqST)
  (⊑-prim wfT' wfU primT primU eqTU)
  =
    ⊥-elim (prim≢object (subst IsPrimitive tyTObj primT))

⊑Co-trans
  (⊑-object wfS wfT tySObj tyTObj prST reqST)
  (⊑-array wfT' wfU tyTArr tyUArr itT itU srTU)
  =
    ⊥-elim (array≢object (trans (sym tyTArr) tyTObj))


⊑Co-trans
  (⊑-object wfS wfT tySObj tyTObj prST reqST)
  (⊑-object wfT' wfU tyTObj' tyUObj prTU reqTU)
  =
    ⊑-object wfS wfU tySObj tyUObj
      (PropsRefine-trans prST prTU)
      (⊆-trans reqST reqTU)
  where
    PropsRefine-trans : ∀ {ps qs rs}
       → PropsRefine Schema⊑Co ps qs
       → PropsRefine Schema⊑Co qs rs
       → PropsRefine Schema⊑Co ps rs
    PropsRefine-trans {ps = []} tt _ = tt
    PropsRefine-trans {ps = (k , s) :: ps'}
       ((t , (lkQ , srST)) , tailPQ)
       prQR
       =
         (u , (lkR , srSU))
         , PropsRefine-trans tailPQ prQR
      where
        pushedQR = PropsRefine-respects-lookup prQR lkQ
        u    = fst pushedQR
        lkR  = fst (snd pushedQR)
        srTU = snd (snd pushedQR)
        srSU = ⊑Co-trans srST srTU
```

---

## 3. Schema refinement as a preorder

So far, we have shown that schema refinement is reflexive and transitive. One caveat is that reflexivity only holds for well-formed schemas, since the proof `⊑Co-refl` requires a `WFSchema` witness.

For this reason, we cannot define the preorder over raw schemas. Instead, we take the carrier to be the type of well-formed schemas: a schema paired with a proof that it is well-formed. We then lift `Schema⊑Co` to act on these pairs, ignoring the proof component.

With this choice of carrier, schema refinement satisfies the axioms of a preorder.

```agda
-- a schema packaged together with a proof that it is well-formed
WFSchemaₛ : Set
WFSchemaₛ = Σ Schema WFSchema

-- lift Schema⊑Co to well-formed schemas
_⊑CoWF_ : WFSchemaₛ → WFSchemaₛ → Set
(s , wfS) ⊑CoWF (t , wfT) = Schema⊑Co s t

Schema⊑Co-preorder : IsPreorder _⊑CoWF_
Schema⊑Co-preorder = record
  { reflexive  = λ { {x = (s , wfS)} → ⊑Co-refl wfS }
  ; transitive = λ { {x = (s , _)} {y = (t , _)} {z = (u , _)} st tu →
                      ⊑Co-trans st tu }
  }
```

This result lets us treat schema refinement as a preorder structure in later semantic arguments, without repeatedly unpacking the underlying reflexivity and transitivity proofs.
