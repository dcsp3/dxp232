# Well-Formedness

This module defines **well-formedness judgements** for the REST DSL introduced in `Syntax.lagda.md`.

The syntax is intentionally permissive: it lets us *write down* any OpenAPI-shaped structure in a uniform way. But not every syntactically constructible term corresponds to a structurally coherent OpenAPI schema. For example, a schema cannot meaningfully be both an `object` (with `properties`) and an `array` (with `items`) at the same time.


**Well-formedness** is the first gate after syntax:
- **Syntax**: what you can express
- **Well-formedness**: what is structurally coherent (OpenAPI-shaped, within our subset)
- **Semantics** (later): what it *means*
- **Compatibility** (later): how meaning behaves under evolution (request vs response)

This module is deliberately conservative. It does not enforce best practices or “nice-to-have” constraints like naming conventions, examples matching types, default values being valid instances, etc. Those are either:
- tooling concerns, or
- semantic concerns (and belong in the next layer).

```agda
module WellFormed where

open import Prelude
open import Syntax
```

## 0. Auxiliary Definitions

We keep a small amount of list-related code in this module. These are not part of the DSL itself, but they let us state well-formedness judgements cleanly.


### 0.1 All-elements predicate

```agda
data All {A : Set} (P : A → Set) : List A → Set where
  all[]  : All P []
  all::_ : ∀ {x xs} → P x → All P xs → All P (x :: xs)
```

### 0.2 Membership (for required fields)

```agda
data _∈_ : String → List String → Set where
  here  : ∀ {x xs} → x ∈ (x :: xs)
  there : ∀ {x y xs} → x ∈ xs → x ∈ (y :: xs)
```

### 0.3 Projections and key extraction
`Schema.properties` and `API.components` are represented as association lists. We often want their keys.

```agda
fst : ∀ {A B : Set} → A × B → A
fst (a , b) = a

snd : ∀ {A B : Set} → A × B → B
snd (a , b) = b

keys : List (String × Schema) → List String
keys [] = []
keys (kv :: rest) = fst kv :: keys rest
```

### 0.4 Primitive Base Types

`Base` includes container kinds (`object`, `array`) as well as primitives. We isolate the primitive cases.

```agda
data IsPrimitive : Base → Set where
  prim-integer : IsPrimitive integer
  prim-string  : IsPrimitive string
  prim-boolean : IsPrimitive boolean
  prim-number  : IsPrimitive number
```

## 1. Well-formed Schemas

A `Schema` in our syntax is a single record that contains fields for all schema shapes:

- `properties`/`required` for objects
- `items` for arrays
- neither for primitives

That’s great for expressing OpenAPI-like documents, but it permits contradictory combinations.

`WFSchema s` enforces shape coherence only:
- If `type = object`, then `items` must be absent, and the object’s fields must themselves be well-formed.
- If `type = array`, then `items` must be present, and object-specific fields must be empty.
- If `type` is primitive, then both array/object fields must be empty.

This mirrors the “structural validity” you would expect from an OpenAPI-shaped schema in our subset. It intentionally does not attempt to validate `enum`, `default`, or `examples` against the schema type, since those are semantic/value-level concerns (handled later).

```agda
data WFSchema : Schema → Set where

  wf-object :
    ∀ {s}
    → Schema.type s ≡ object
    → Schema.items s ≡ nothing
    → All (λ kv → WFSchema (snd kv)) (Schema.properties s)
    → All (λ r → r ∈ keys (Schema.properties s)) (Schema.required s)
    → WFSchema s

  wf-array :
    ∀ {s item}
    → Schema.type s ≡ array
    → Schema.items s ≡ just item
    → WFSchema item
    → Schema.properties s ≡ []
    → Schema.required s ≡ []
    → WFSchema s

  wf-prim :
    ∀ {s}
    → IsPrimitive (Schema.type s)
    → Schema.items s ≡ nothing
    → Schema.properties s ≡ []
    → Schema.required s ≡ []
    → WFSchema s
```
