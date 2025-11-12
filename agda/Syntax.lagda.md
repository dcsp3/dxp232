# Syntax
This module defines the core syntax for our REST DSL, aligning with the subset of the OpenAPI 3.1 Specification selected for formalisation.

The syntax is grouped as follows:

| DSL Layer | Contents | Corresponding OpenAPI Section |
|----------------|--------------|-----------------------------------|
| HTTP Primitives | Methods and statuses | Core HTTP concepts (used throughout the spec) |
| Data Level | Schemas and base types | `components/schemas` |
| Operation Level | Parameters, paths, request bodies, responses, endpoints | `paths` and their nested operations |
| API Level | Top-level API definition and metadata | Root OpenAPI document (`info`, `paths`, `components`) |

---

```agda
module Syntax where

open import Prelude
```

## 1. HTTP Primitives
These define the basic HTTP constants used across the DSL.
They include supported methods and standard response statuses.

### 1.1 Methods

```agda
data Method : Set where
  GET POST PUT DELETE PATCH : Method
```

### 1.2 Statuses

```agda
data Status : Set where
  OK         : Status   -- 200
  BadRequest : Status   -- 400
  NotFound   : Status   -- 404
  NoContent  : Status   -- 204
```

---

## 2. Data Level

Defines the structure of the information exchanged between client and server. It captures how OpenAPI represents schemas by describing data shapes, types, and constraints.

### 2.1 Base Types
Primitive and container types supported by the DSL.

```agda
data Base : Set where
  integer string boolean number object array : Base
```

### 2.2 Schema Definition
A Schema describes the shape of data defined at the type level.
It is declared as inductive, since schemas are finite recursive structures.
This corresponds directly to OpenAPI’s `components/schemas` definitions.

```agda 
record Schema : Set where
  inductive
  field
    type        : Base                      -- "object", "array", or primitive
    properties  : List (String × Schema)    -- fields for objects
    required    : List String               -- required field names
    items       : Maybe Schema              -- element type for arrays

    enum        : Maybe (List String)       -- allowed values (if constrained)
    default     : Maybe String              -- default literal (if any)
    description : Maybe String              -- optional documentation
    examples    : List String               -- example literals
```

---

## 3. Operation Level

---

## 4. API Level

## 3. Schemas
The `Schema` type represents the shape of the data exchanged between client and server.
Each schema specifies:
- a **type** (object, array, or a primitive like string/integer)
- **properties** that belong to it (e.g., fields in objects)
- a list of **required** fields
- the **items** it contains (for arrays)

along with other optional fields to store metadata.



## 4. Request Bodies (Dependent on Method)
`Body` is indexed by the HTTP method, encoding REST rules in the type itself.

```agda
data Body : Method → Set where
  NoBody  : Body GET
  HasBody : Schema → Body POST
```

This ensures:
- `GET` requests cannot have a body
- `POST` requests must carry a payload defined by a `Schema`

Attempting to assign a body to `GET` will result in a **type error**; enforcing REST correctness at compile time.

## 5. Response Cases
Each response pairs a status code with its payload schema

```agda
data RespCase : Set where
  Case : Status → Schema → RespCase
```

We represent endpoint responses as a *list* of `RespCase` values instead of a function `Status → Schema`.

## 6. Endpoint Specification
An `Endpoint` describes a single REST endpoint.

```agda
record Endpoint : Set where
  field
    path      : String        -- Route (e.g. "/todos/{id}")
    method    : Method        -- HTTP method
    body      : Body method   -- Request Body (dependent on method)
    responses : List RespCase -- Mapping of statuses to schemas
```

Example:

