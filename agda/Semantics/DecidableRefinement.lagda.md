# Decidable Refinement

We show that refinement is decidable for well-formed specifications. More precisely, given two well-formed schemas, endpoints, or APIs, we can effectively decide whether the refinement relation holds.

The construction proceeds bottom-up. We first decide schema refinement by structural recursion on schema shape. We then lift this to endpoints, aligning parameters, request bodies, and responses using the schema decision procedure. Finally, we lift again to APIs by aligning components and endpoints via lookup.

All procedures are constructive and operate over finite structures. They rely only on decidable equality for syntactic identifiers and recursive checks on strictly smaller substructures.

Well-formedness is essential here. It guarantees uniqueness of keys and removes ambiguous lookup cases, ensuring that alignment is computable.

The result is an executable notion of compatibility: for any two well-formed APIs, we can decide whether one safely refines the other.

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
  using (⊑Co-refl; ⊑Co-trans; prim≢array; prim≢object)

open Σ using (fst ; snd)
```

---

## 1. Decidability of Covariant Schema Refinement

We decide covariant schema refinement by structural recursion on schema shape. The procedure mirrors the constructors of `Schema⊑Co`, with the object case requiring additional checks for property preservation and required-field inclusion.

---

### 1.1 Auxiliary List Decisions

### Decidable membership

```agda
_∈?_ : (x : String) → (xs : List String) → Dec (x ∈ xs)
_∈?_ x [] = no (λ ())
_∈?_ x (y :: ys) with x ≟ y
... | yes refl = yes here
... | no x≢y
    with x ∈? ys
...   | yes p  = yes (there p)
...   | no  np =
          no (λ {
            here      → x≢y refl
          ; (there q) → np q
          })
```

### Decidable subset

```agda
_⊆?_ : (xs ys : List String) → Dec (xs ⊆ ys)
_⊆?_ [] ys = yes all[]
_⊆?_ (x :: xs) ys
  with x ∈? ys
... | no x∉ys =
      no (λ {
        (all::_ px _) → x∉ys px
      })

... | yes x∈ys
    with xs ⊆? ys
...   | no xs⊈ys =
          no (λ {
            (all::_ _ rest) → xs⊈ys rest
          })
...   | yes xs⊆ys =
          yes (all::_ x∈ys xs⊆ys)
```

---

### 1.2 Decidable Property Refinement

To decide the object case of schema refinement, we need to check that every property in the old schema is present in the new schema with a refining type. We decide this by recursion over the old property list, using `lookupProp` to align entries and the main schema decision procedure recursively.

```agda
PropsRefine? :
    (∀ s t → Dec (Schema⊑Co s t))
  → (ps qs : List (String × Schema))
  → Dec (PropsRefine Schema⊑Co ps qs)
PropsRefine? R? [] qs = yes tt
PropsRefine? R? ((k , s) :: ps) qs
  with lookupProp k qs
... | nothing = no (λ p → just≢nothing (sym (fst (snd (fst p)))))
... | just t
  with R? s t
... | no ¬r = no (λ p →
  let sn   = fst (fst p)
      lk   = fst (snd (fst p))
      r'   = snd (snd (fst p))
      sn≡t = sym (just-inj lk)
  in ¬r (subst (Schema⊑Co s) sn≡t r'))
... | yes r
  with PropsRefine? R? ps qs
... | no ¬rest = no (λ p → ¬rest (snd p))
... | yes rest = yes ((t , (refl , r)) , rest)
```

---

### 1.3 Decidable Covariant Schema Refinement

```agda
Schema⊑Co? :
  ∀ {s t}
  → WFSchema s
  → WFSchema t
  → Dec (Schema⊑Co s t)
```

### Primitive cases

```agda
Schema⊑Co? {s} {t}
  wfS@(wf-prim primS _ _ _)
  wfT@(wf-prim primT _ _ _)
  with Base≟ (Schema.type s) (Schema.type t)
... | yes refl =
      yes (⊑-prim wfS wfT primS primT refl)

... | no neq =
      no impossible
  where
    impossible : Schema⊑Co s t → ⊥
    impossible (⊑-prim _ _ _ _ eq) = neq eq
    impossible (⊑-array _ _ tyS _ _ _ _) =
      prim≢array (subst IsPrimitive tyS primS)
    impossible (⊑-object _ _ tyS _ _ _) =
      prim≢object (subst IsPrimitive tyS primS)
      
Schema⊑Co? {s} {t}
  (wf-prim primS _ _ _)
  (wf-array tyT _ _ _ _) =
  no impossible
  where
    impossible : Schema⊑Co s t → ⊥

    impossible (⊑-prim _ _ _ _ eq) =
      prim≢array
        (subst IsPrimitive
          (trans eq tyT)
          primS)

    impossible (⊑-array _ _ tyS _ _ _ _) =
      prim≢array (subst IsPrimitive tyS primS)

    impossible (⊑-object _ _ tyS _ _ _) =
      prim≢object (subst IsPrimitive tyS primS)

Schema⊑Co? {s} {t}
  (wf-prim primS _ _ _)
  (wf-object tyT _ _ _ _ _) =
  no impossible
  where
    impossible : Schema⊑Co s t → ⊥

    impossible (⊑-prim _ _ _ _ eq) =
      prim≢object
        (subst IsPrimitive
          (trans eq tyT)
          primS)

    impossible (⊑-array _ _ tyS _ _ _ _) =
      prim≢array (subst IsPrimitive tyS primS)

    impossible (⊑-object _ _ tyS _ _ _) =
      prim≢object (subst IsPrimitive tyS primS)
```

### Array cases


