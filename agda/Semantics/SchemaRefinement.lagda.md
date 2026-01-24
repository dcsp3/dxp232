# Schema Refinement

This module defines the semantic backbone of compatibility: a variance-aware refinement relation on schemas.

Refinement is defined structurally (by schema shape) and only for well-formed schemas, so we never reason about incoherent combinations of object/array/primitive fields.

---

```agda
module Semantics.SchemaRefinement where

open import Prelude
open import Syntax
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

We define the judgement first, and then introduce its refinement rules incrementally.

```agda
data Schema⊑Co : Schema → Schema → Set where
```

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
