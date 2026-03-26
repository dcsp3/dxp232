# Schema Refinement

This module defines the semantic backbone of compatibility: a variance-aware refinement relation on schemas.

Refinement is defined structurally (by schema shape) and only for well-formed schemas, so we never reason about incoherent combinations of object/array/primitive fields.

---

```agda
module Semantics.SchemaRefinement where

open import Prelude
open import Syntax.Syntax

open import WellFormed.Core
open import Semantics.Variance
```

## 1. Covariant schema refinement

The core semantic judgement is **covariant schema refinement**.

`Schema⊑Co old new` should be read as:

> `new` is a safe replacement for `old` in covariant (client-observed) positions.

This judgement is defined by constructors corresponding to the different schema shapes.
Contravariant refinement (used for requests) will later be obtained by flipping the direction of this relation using variance.

```agda
lookupProp : String → List (String × Schema) → Maybe Schema
lookupProp k [] = nothing
lookupProp k ((k' , s) :: ps) with k ≟ k'
... | yes _ = just s
... | no  _ = lookupProp k ps

-- All old properties are preserved and refined in the new object, parameterised by a relation on schemas.
PropsRefine :
    (Schema → Schema → Set)
  → List (String × Schema)
  → List (String × Schema)
  → Set
PropsRefine R [] newProps = ⊤
PropsRefine R ((k , so) :: oldProps) newProps =
  (∃ (λ sn → (lookupProp k newProps ≡ just sn) × (R so sn)))
  × PropsRefine R oldProps newProps
```

```agda
data Schema⊑Co : Schema → Schema → Set where
```

---

## 2. Refinement rules

### 2.1 Primitive schemas

A primitive schema refines another only when they share the same base type.

```agda
  ⊑-prim :
      ∀ {s t}
    → WFSchema s
    → WFSchema t
    → IsPrimitive (Schema.type s)
    → IsPrimitive (Schema.type t)
    → Schema.type s ≡ Schema.type t
    → Schema⊑Co s t
```

### 2.2 Array schemas

Array schemas refine covariantly when their item schemas refine covariantly.

```agda
  ⊑-array :
      ∀ {s t si ti}
    → WFSchema s
    → WFSchema t
    → Schema.type s ≡ array
    → Schema.type t ≡ array
    → Schema.items s ≡ just si
    → Schema.items t ≡ just ti
    → Schema⊑Co si ti
    → Schema⊑Co s t
```

### 2.3 Object schemas

In covariant positions (responses), refinement must preserve everything that existing clients might read. In particular, a client may read any field, but can only rely on presence for fields listed in `required`. Removing or changing such fields would be breaking.

Covariant object refinement therefore requires that every old property is still present in the new object with a refining schema (`PropsRefine`), and that the required set only grows.

```agda
  ⊑-object :
    ∀ {s t}
    → WFSchema s
    → WFSchema t
    → Schema.type s ≡ object
    → Schema.type t ≡ object
    → PropsRefine Schema⊑Co
       (Schema.properties s)
       (Schema.properties t)
    → Schema.required s ⊆ Schema.required t
    → Schema⊑Co s t
```

---

## 3. Variance-aware schema refinement

- For covariant positions (responses), refinement is exactly `Schema⊑Co`.
- For contravariant positions (requests), refinement is obtained by reversing the direction.

```agda
Schema⊑ : Variance → Schema → Schema → Set
Schema⊑ Co     old new = Schema⊑Co old new
Schema⊑ Contra old new = Schema⊑Co new old
```
