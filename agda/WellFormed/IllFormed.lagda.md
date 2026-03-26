# Ill-Formedness Witnesses

This module defines the witness types we use when well-formedness checks fail.

The design is compositional. We do not list every possible malformed API shape as a separate constructor. Instead, each constructor corresponds to a rule violation, and larger witnesses can contain smaller ones.

That gives the checker a clean result shape:

- a positive proof that a specification is well-formed, or
- a positive witness showing where it is ill-formed.

```agda
module WellFormed.IllFormed where

open import Prelude
open import Syntax.Syntax

open import WellFormed.Core
```

## 1. Generic Duplicate Witnesses

Several judgements require uniqueness (property keys, required fields, path placeholders, parameter keys, response statuses, component names, endpoint keys).

`HasDuplicate` captures this directly: either the head is duplicated in the tail, or the duplicate is in the tail.

```agda
data HasDuplicate {A : Set} : List A → Set where
  dup-here  : ∀ {x xs} → x ∈ xs → HasDuplicate (x :: xs)
  dup-there : ∀ {x xs} → HasDuplicate xs → HasDuplicate (x :: xs)
```

## 2. Primitive / Non-Primitive Base Classifiers

Parameters in this DSL are restricted to primitive base types. `NonPrimitive` is a small helper witness used when that restriction is violated.

```agda
data NonPrimitive : Base → Set where
  nonprim-object : NonPrimitive object
  nonprim-array  : NonPrimitive array
```

## 3. Ill-Formed Schemas

`WFSchema` has three intended shapes: object, array, and primitive. `SchemaIllFormed` records exactly which shape-specific obligation failed.

```agda
data SchemaIllFormed : Schema → Set where

  prim-has-items :
    ∀ {s item}
    → IsPrimitive (Schema.type s)
    → Schema.items s ≡ just item
    → SchemaIllFormed s

  prim-has-properties :
    ∀ {s}
    → IsPrimitive (Schema.type s)
    → (k : String)
    → (child : Schema)
    → (k , child) ∈ Schema.properties s
    → SchemaIllFormed s

  prim-has-required :
    ∀ {s}
    → IsPrimitive (Schema.type s)
    → (k : String)
    → k ∈ Schema.required s
    → SchemaIllFormed s

  array-missing-items :
    ∀ {s}
    → Schema.type s ≡ array
    → Schema.items s ≡ nothing
    → SchemaIllFormed s

  array-item-ill-formed :
    ∀ {s item}
    → Schema.type s ≡ array
    → Schema.items s ≡ just item
    → SchemaIllFormed item
    → SchemaIllFormed s

  array-has-properties :
    ∀ {s}
    → Schema.type s ≡ array
    → (k : String)
    → (child : Schema)
    → (k , child) ∈ Schema.properties s
    → SchemaIllFormed s

  array-has-required :
    ∀ {s}
    → Schema.type s ≡ array
    → (k : String)
    → k ∈ Schema.required s
    → SchemaIllFormed s

  object-has-items :
    ∀ {s item}
    → Schema.type s ≡ object
    → Schema.items s ≡ just item
    → SchemaIllFormed s

  object-property-ill-formed :
    ∀ {s}
    → Schema.type s ≡ object
    → (k : String)
    → (child : Schema)
    → (k , child) ∈ Schema.properties s
    → SchemaIllFormed child
    → SchemaIllFormed s

  object-missing-required :
    ∀ {s}
    → Schema.type s ≡ object
    → (k : String)
    → k ∈ Schema.required s
    → k ∉ keys (Schema.properties s)
    → SchemaIllFormed s

  object-duplicate-properties :
    ∀ {s}
    → Schema.type s ≡ object
    → HasDuplicate (keys (Schema.properties s))
    → SchemaIllFormed s

  object-duplicate-required :
    ∀ {s}
    → Schema.type s ≡ object
    → HasDuplicate (Schema.required s)
    → SchemaIllFormed s
```

## 4. Ill-Formed Parameters

`ParameterIllFormed` covers the two parameter-side rule violations in this fragment.

```agda
data ParameterIllFormed : Parameter → Set where

  path-param-not-required :
    ∀ {p}
    → Parameter.location p ≡ path
    → Parameter.required p ≡ false
    → ParameterIllFormed p

  param-nonprimitive :
    ∀ {p}
    → NonPrimitive (Parameter.schema p)
    → ParameterIllFormed p
```

## 5. Ill-Formed Paths

`PathIllFormed` captures path/parameter mismatches and duplicate placeholders.

```agda
data PathIllFormed : Path → List Parameter → Set where

  duplicate-placeholder :
    ∀ {p ps}
    → HasDuplicate (pathPlaceholders p)
    → PathIllFormed p ps

  placeholder-not-declared :
    ∀ {p ps}
    → (x : String)
    → x ∈ pathPlaceholders p
    → x ∉ pathParamNames ps
    → PathIllFormed p ps

  orphan-path-parameter :
    ∀ {p ps}
    → (x : String)
    → x ∈ pathParamNames ps
    → x ∉ pathPlaceholders p
    → PathIllFormed p ps
```

## 6. Ill-Formed Bodies and Responses

These are thin wrappers that lift schema ill-formedness into body and response positions.

```agda
data BodyIllFormed : ∀ {m} → Body m → Set where
  post-body-ill-formed : ∀ {s} → SchemaIllFormed s → BodyIllFormed (HasBody s)
  put-body-ill-formed  : ∀ {s} → SchemaIllFormed s → BodyIllFormed (HasBodyU s)
  patch-body-ill-formed : ∀ {s} → SchemaIllFormed s → BodyIllFormed (HasBodyP s)

data ResponseIllFormed : Response → Set where
  response-schema-ill-formed :
    ∀ {st s}
    → SchemaIllFormed s
    → ResponseIllFormed (response st s)
```

## 7. Ill-Formed Endpoints

`EndpointIllFormed` bundles the endpoint-level failure modes: bad path alignment, bad subcomponents, or duplicate keys.

```agda
data EndpointIllFormed : Endpoint → Set where

  endpoint-path-ill-formed :
    ∀ {e}
    → PathIllFormed (Endpoint.route e) (Endpoint.parameters e)
    → EndpointIllFormed e

  endpoint-parameter-ill-formed :
    ∀ {e}
    → (p : Parameter)
    → p ∈ Endpoint.parameters e
    → ParameterIllFormed p
    → EndpointIllFormed e

  endpoint-duplicate-parameters :
    ∀ {e}
    → HasDuplicate (paramKeys (Endpoint.parameters e))
    → EndpointIllFormed e

  endpoint-body-ill-formed :
    ∀ {e}
    → BodyIllFormed (Endpoint.body e)
    → EndpointIllFormed e

  endpoint-response-ill-formed :
    ∀ {e}
    → (r : Response)
    → r ∈ Endpoint.responses e
    → ResponseIllFormed r
    → EndpointIllFormed e

  endpoint-duplicate-statuses :
    ∀ {e}
    → HasDuplicate (respKeys (Endpoint.responses e))
    → EndpointIllFormed e
```

## 8. Ill-Formed APIs

At the API level we either point to an ill-formed component/endpoint or to a top-level duplicate-key issue.

```agda
data APIIllFormed : API → Set where

  api-component-ill-formed :
    ∀ {api}
    → (k : String)
    → (s : Schema)
    → (k , s) ∈ API.components api
    → SchemaIllFormed s
    → APIIllFormed api

  api-duplicate-components :
    ∀ {api}
    → HasDuplicate (componentKeys api)
    → APIIllFormed api

  api-endpoint-ill-formed :
    ∀ {api}
    → (e : Endpoint)
    → e ∈ API.paths api
    → EndpointIllFormed e
    → APIIllFormed api

  api-duplicate-endpoints :
    ∀ {api}
    → HasDuplicate (endpointKeys (API.paths api))
    → APIIllFormed api
```
