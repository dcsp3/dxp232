# Decidable Refinement

Refinement and drift describe the same situation from opposite directions. Given two well-formed specifications, we can either build a proof that one safely refines the other, or point to a specific structural change that breaks compatibility.

The construction works bottom-up. We start at the schema level, deciding refinement by structural recursion on shape and returning either a `Schema⊑Co` proof or a `SchemaDrift` witness. We then lift this to endpoints by checking parameters, request bodies, and responses. Finally, we lift again to APIs by aligning components and endpoints via lookup.

All checks are constructive and run over finite structures. They depend only on decidable equality for identifiers and recursive calls on smaller pieces of the specification. Well-formedness plays a crucial role: it guarantees uniqueness of keys and ensures that every alignment step is deterministic and computable.

```agda
module Semantics.DecidableRefinement where

open import Prelude
open import Syntax.Syntax
open import Syntax.Decidable

open import WellFormed.Core
open import WellFormed.Lemmas

open import Semantics.Variance

open import Semantics.SchemaRefinement
open import Semantics.SchemaRefinementProperties
  using (lookupProp-here; lookupProp-skip; lookupProp-∉-nothing; ⊑Co-refl; ⊑Co-trans; prim≢array; prim≢object)

open import Semantics.Drift

open import Semantics.EndpointRefinement
open import Semantics.APIRefinement

open Σ using (fst ; snd)
```

## 1. Decidability of Covariant Schema Refinement

We decide covariant schema refinement by structural recursion on schema shape. The procedure follows the constructors of `Schema⊑Co`. When refinement succeeds we return `inl` with a proof; when it fails we return `inr` with a `SchemaDrift` witness explaining the structural violation.

### 1.1 Decidable Property Refinement

The object case reduces to property alignment. For each property in the old schema, we check that it exists in the new schema and that its schema refines recursively. Failure is recorded as a `PropertyFailure`, which is later converted into a `SchemaDrift`.

`PropsRefine?` and `Schema⊑Co?` are mutually recursive because object refinement requires recursive schema checks on property types.

### Helpers

```agda
data PropertyFailure
  (ps qs : List (String × Schema)) : Set where

  MissingProperty :
      (k : String)
    → lookupProp k ps ≢ nothing
    → lookupProp k qs ≡ nothing
    → PropertyFailure ps qs

  NestedDrift :
      (k : String)
      (si ti : Schema)
    → lookupProp k ps ≡ just si
    → lookupProp k qs ≡ just ti
    → SchemaDrift si ti
    → PropertyFailure ps qs
```

```agda
lookupProp-wf : ∀ {k s ps} → All WFSchema (values ps) → lookupProp k ps ≡ just s → WFSchema s
lookupProp-wf {k} {s} {[]} _ ()
lookupProp-wf {k} {s} {(k' , s') :: ps} (all::_ wfS wfRest) lk
  with k ≟ k'
... | yes refl = subst WFSchema (just-inj lk) wfS
... | no  _    = lookupProp-wf wfRest lk
```

```agda
liftPropertyFailure : ∀ {k s ps qs} → k ∉ keys ps → PropertyFailure ps qs → PropertyFailure ((k , s) :: ps) qs
liftPropertyFailure {k} k∉ (MissingProperty k' notNoth missing)
  with k' ≟ k
... | no  k'≢k = MissingProperty k' (λ contra → notNoth (trans (sym (lookupProp-skip k'≢k)) contra)) missing
... | yes refl = ⊥-elim (notNoth (lookupProp-∉-nothing k∉))
liftPropertyFailure {k} k∉ (NestedDrift k' si ti lkPs lkQt d)
  with k' ≟ k
... | no  k'≢k = NestedDrift k' si ti (trans (lookupProp-skip k'≢k) lkPs) lkQt d
... | yes refl = ⊥-elim (just≢nothing (trans (sym lkPs) (lookupProp-∉-nothing k∉)))
```

```agda
propertyFailure→SchemaDrift :
 ∀ {s t}
  → Schema.type s ≡ object
  → Schema.type t ≡ object
  → PropertyFailure (Schema.properties s)
                    (Schema.properties t)
  → SchemaDrift s t

propertyFailure→SchemaDrift {s} {t} tyS tyT
  (MissingProperty k notNoth missing) =
    PropertyRemoved tyS tyT notNoth missing

propertyFailure→SchemaDrift tyS tyT
  (NestedDrift k si ti lkPs lkQt d) =
    PropertyDrift tyS tyT lkPs lkQt d
```

### Decision Procedure

```agda
mutual
  PropsRefine? :
      (ps qs : List (String × Schema))
    → All WFSchema (values ps)
    → All WFSchema (values qs)
    → Unique (keys ps)
    → PropsRefine Schema⊑Co ps qs
      ∔ PropertyFailure ps qs

  PropsRefine? [] qs _ _ _ = inl tt

  PropsRefine? ((k , s) :: ps) qs (all::_ wfS wfRest) wfQs (uniq::_ k∉tail uniqTail)
    with lookupProp k qs in eq

  -- Property missing in new schema
  ... | nothing =
        inr (MissingProperty k (λ contra → just≢nothing (trans (sym lookupProp-here) contra)) eq)

  -- Property exists
  ... | just t
    with Schema⊑Co? wfS (lookupProp-wf wfQs eq)
    
  -- Nested schema drift
  ... | inr d =
        inr (NestedDrift k s t lookupProp-here eq d)

  -- Nested refinement succeeds → recurse
  ... | inl r
    with PropsRefine? ps qs wfRest wfQs uniqTail

  -- Tail failure propagates
  ... | inr pf =
        inr (liftPropertyFailure k∉tail pf)

  -- Everything succeeds
  ... | inl rest =
        inl ((t , (refl , r)) , rest)
```

---

### 1.2 Decidable Covariant Schema Refinement

```agda
  Schema⊑Co? :
    ∀ {s t}
    → WFSchema s
    → WFSchema t
    → Schema⊑Co s t ∔ SchemaDrift s t
```

### Primitives

```agda
  Schema⊑Co? {s} {t}
    wfS@(wf-prim primS _ _ _)
    wfT@(wf-prim primT _ _ _)
    with Base≟ (Schema.type s) (Schema.type t)
  ... | yes refl =
        inl (⊑-prim wfS wfT primS primT refl)

  ... | no neq =
        inr (PrimitiveChanged primS primT neq)
```

### Arrays

```agda
  Schema⊑Co? {s} {t}
    wfS@(wf-array tyS itemsS wfItemS _ _)
    wfT@(wf-array tyT itemsT wfItemT _ _)
    with Schema⊑Co? wfItemS wfItemT
  ... | inl r =
        inl (⊑-array wfS wfT tyS tyT itemsS itemsT r)

  ... | inr d =
        inr (ArrayItemDrift tyS tyT itemsS itemsT d)
```

### Objects

```agda
  Schema⊑Co? {s} {t}
    wfS@(wf-object tyS _ wfPropsS wfReqS uniqS reqUniqS)
    wfT@(wf-object tyT _ wfPropsT wfReqT uniqT reqUniqT)
    with PropsRefine?
           (Schema.properties s)
           (Schema.properties t)
           wfPropsS
           wfPropsT
           uniqS
  ... | inr pf =
        inr (propertyFailure→SchemaDrift tyS tyT pf)

  ... | inl pr
    with Schema.required s ⊆? Schema.required t
  ...   | no subFail =
          let (k , (k∈ , k∉)) = ⊆-counterexample subFail
          in inr (RequiredFieldRemoved tyS tyT k∈ k∉)

  ...   | yes sub =
          inl (⊑-object wfS wfT tyS tyT pr sub)
```

### Shape mismatches

```agda
  Schema⊑Co? (wf-prim primS _ _ _) (wf-array tyT _ _ _ _) =
    inr (ShapeMismatch (λ eq → prim≢array (subst IsPrimitive (trans eq tyT) primS)))

  Schema⊑Co? (wf-prim primS _ _ _) (wf-object tyT _ _ _ _ _) =
    inr (ShapeMismatch (λ eq → prim≢object (subst IsPrimitive (trans eq tyT) primS)))

  Schema⊑Co? (wf-array tyS _ _ _ _) (wf-prim primT _ _ _) =
    inr (ShapeMismatch (λ eq → prim≢array (subst IsPrimitive (trans (sym eq) tyS ) primT)))

  Schema⊑Co? (wf-array tyS _ _ _ _) (wf-object tyT _ _ _ _ _) =
    inr (ShapeMismatch (λ eq → array≢object (trans (sym tyS) (trans eq tyT))))

  Schema⊑Co? (wf-object tyS _ _ _ _ _) (wf-prim primT _ _ _) =
    inr (ShapeMismatch (λ eq → prim≢object (subst IsPrimitive (trans (sym eq) tyS) primT)))

  Schema⊑Co? (wf-object tyS _ _ _ _ _) (wf-array tyT _ _ _ _) =
    inr (ShapeMismatch (λ eq → array≢object (trans (sym tyT) (trans (sym eq) tyS))))
```

The procedure is total and structurally recursive on the schema shape. Each negative branch corresponds directly to one of the constructors of `SchemaDrift`, ensuring that failure always carries a structured explanation.

---
