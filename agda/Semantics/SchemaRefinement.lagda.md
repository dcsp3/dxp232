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
Contravariant refinement (used for requests) will later be obtained by flipping the direction
of this relation using variance.

Before introducing the refinement rules themselves, we define a small amount of
supporting machinery used by the object case.

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

With these definitions in place, we can now define covariant schema refinement itself.

```agda
data Schema⊑Co : Schema → Schema → Set where
```

---

## 2. Refinement rules

### 2.1 Primitive schemas

Primitive schemas refine conservatively.

For now, a primitive schema safely refines another only when they share the same base type.
This reflects the fact that a client expecting a particular primitive value (e.g. a string)
cannot safely consume a different primitive type.

More permissive refinements (such as allowing `integer ⊑ number`) can be added later as
additional constructors, without changing the overall structure.


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

Intuitively, a client that can consume elements of a certain shape can also
consume arrays whose elements are refined versions of that shape.

Well-formedness ensures that array schemas always carry an item schema, so
this rule is structurally well-defined.


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

Objects are the main non-trivial case of schema refinement.

In covariant positions (responses), refinement must preserve everything that existing
clients might read. In particular, a client may read any field, but can only rely on presence
for fields listed in `required`. Removing or changing such fields would therefore be breaking.

For this reason, covariant object refinement enforces the following conditions:

- Preservation of properties: every property present in the old object must still
be present in the new object.
- Recursive refinement: for each preserved property, the corresponding field schema
must itself refine covariantly.
- Extensibility: the new object may introduce additional properties, which existing
clients can safely ignore.
- Preservation of requiredness: every required field in the old object remains required in the new object.

These conditions are expressed using the auxiliary predicate `PropsRefine`, which states
that all properties of one object are preserved and related by a given schema relation.
Using this predicate, covariant object refinement is defined as a constructor of
`Schema⊑Co`.

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

Now that we have defined schema refinement in one direction, we can recover full notion using variance.

- For covariant positions (such as responses), refinement is exactly `Schema⊑Co`.
- For contravariant positions (such as requests), refinement is obtained by reversing the direction.

We capture this with a simple variance-indexed wrapper.

```agda
Schema⊑ : Variance → Schema → Schema → Set
Schema⊑ Co     old new = Schema⊑Co old new
Schema⊑ Contra old new = Schema⊑Co new old
```
