# Testing Decidable Schema Well-Formedness Checker

This module demonstrates the `WFSchema?` decision procedure on concrete examples.

```agda
module WellFormed.DecidableTest where

open import Prelude
open import Syntax.Syntax
open import WellFormed.Core
open import WellFormed.IllFormed
open import WellFormed.Decidable

-- Helper to display results
data TestResult : Set where
  success : String → TestResult
  failure : String → TestResult
```

## Helper Functions

```agda
showResult : ∀ {s} (r : WFSchema s ∔ SchemaIllFormed s) → TestResult
showResult (inl _) = success "✓ Schema is well-formed"
showResult (inr (prim-has-items _ _)) = 
  failure "✗ Primitive schema has items field"
showResult (inr (prim-has-properties _ _ _ _)) = 
  failure "✗ Primitive schema has properties"
showResult (inr (prim-has-required _ _ _)) = 
  failure "✗ Primitive schema has required field"
showResult (inr (array-missing-items _ _)) = 
  failure "✗ Array schema missing items field"
showResult (inr (array-item-ill-formed _ _ _)) = 
  failure "✗ Array's item schema is ill-formed"
showResult (inr (array-has-properties _ _ _ _)) = 
  failure "✗ Array schema has properties"
showResult (inr (array-has-required _ _ _)) = 
  failure "✗ Array schema has required field"
showResult (inr (object-has-items _ _)) = 
  failure "✗ Object schema has items field"
showResult (inr (object-property-ill-formed _ _ _ _ _)) = 
  failure "✗ Object has ill-formed property"
showResult (inr (object-missing-required _ _ _ _)) = 
  failure "✗ Object required field not in properties"
showResult (inr (object-duplicate-properties _ _)) = 
  failure "✗ Object has duplicate property keys"
showResult (inr (object-duplicate-required _ _)) = 
  failure "✗ Object has duplicate required fields"
```

## 1. Well-formed Examples

### 1.1 Simple primitive schema (integer)

```agda
example-int : Schema
example-int = record
  { type        = integer
  ; properties  = []
  ; required    = []
  ; items       = nothing
  ; enum        = nothing
  ; default     = nothing
  ; description = nothing
  ; examples    = []
  }

test-int : WFSchema example-int ∔ SchemaIllFormed example-int
test-int = WFSchema? example-int

result-int : TestResult
result-int = showResult test-int
```

## 2. Ill-formed Examples

### 2.1 Array with missing items (should fail)

```agda
example-bad-arr : Schema
example-bad-arr = record
  { type        = array
  ; properties  = []
  ; required    = []
  ; items       = nothing
  ; enum        = nothing
  ; default     = nothing
  ; description = nothing
  ; examples    = []
  }

test-bad-arr : WFSchema example-bad-arr ∔ SchemaIllFormed example-bad-arr
test-bad-arr = WFSchema? example-bad-arr

result-bad-arr : TestResult
result-bad-arr = showResult test-bad-arr
```

### 2.2 Primitive with items (should fail)

```agda
item-schema : Schema
item-schema = record
  { type        = string
  ; properties  = []
  ; required    = []
  ; items       = nothing
  ; enum        = nothing
  ; default     = nothing
  ; description = nothing
  ; examples    = []
  }

example-bad-prim-items : Schema
example-bad-prim-items = record
  { type        = integer
  ; properties  = []
  ; required    = []
  ; items       = just item-schema
  ; enum        = nothing
  ; default     = nothing
  ; description = nothing
  ; examples    = []
  }

test-bad-prim-items : WFSchema example-bad-prim-items ∔ SchemaIllFormed example-bad-prim-items
test-bad-prim-items = WFSchema? example-bad-prim-items

result-bad-prim-items : TestResult
result-bad-prim-items = showResult test-bad-prim-items
```
