# Schema Refinement Properties

We show that covariant schema refinement is:

- **reflexive**: on well-formed schemas, and
- **transitive**.

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

Every well-formed schema safely refines itself.

```agda
⊑Co-refl : ∀ {s} → WFSchema s → Schema⊑Co s s
```

### 1.1 Lookup helpers

For objects, we first record some basic facts about property lookup.

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

To build the object case of `⊑Co-refl`, we show that a well-formed property list refines itself field-by-field.

This relies on uniqueness of property keys, so that lookup behaves deterministically.

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

Schema refinement composes across intermediate schemas.

If `s ⊑ t` and `t ⊑ u`, then `s ⊑ u`.

---

### 2.1 Transporting lookups across property refinement

To compose object refinement, we first show that successful lookup is preserved across `PropsRefine`.

```agda
PropsRefine-respects-lookup :
    ∀ {k s ps qs}
  → PropsRefine Schema⊑Co ps qs
  → lookupProp k ps ≡ just s
  → ∃ (λ t → (lookupProp k qs ≡ just t) × (Schema⊑Co s t))

PropsRefine-respects-lookup {ps = []} tt ()

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

Reflexivity requires a `WFSchema` witness, so the preorder is defined over well-formed schemas rather than raw schemas.

We therefore take the carrier to be schemas paired with well-formedness proofs, and lift `Schema⊑Co` to this type.

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
