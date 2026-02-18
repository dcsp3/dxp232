# Syntax
This module defines the core syntax for our REST DSL, aligning with the subset of the OpenAPI 3.1 Specification selected for formalisation.

The syntax is grouped as follows:

| DSL Layer | Contents | Corresponding OpenAPI Section |
|----------------|--------------|-----------------------------------|
| HTTP Primitives | Methods and statuses | Core HTTP concepts (used throughout the spec) |
| Data Level | Schemas and base types | `components/schemas` |
| Operation Level | Parameters, paths, request bodies, responses, endpoints | `paths` and their nested operations |
| API Level | Top-level API definition and metadata | Root OpenAPI document (`info`, `paths`, `components`) |


>A direct translation of an OpenAPI spec to this syntax is given in [`ExampleTodoAPI.lagda.md`](./ExampleTodoAPI.lagda.md).

---

```agda
module Syntax.Syntax where

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

Defines how data is used within individual REST operations.
This layer corresponds to the `paths` and `operations` objects in OpenAPI.

### 3.1 Parameters
Parameters represent input values passed to an operation through the URL path or query string.  
Each parameter includes its name, where it appears, whether it is required, and its type.

```agda
data ParamLocation : Set where
  path query : ParamLocation

record Parameter : Set where
  field
    name     : String
    location : ParamLocation   -- corresponds to OpenAPI's 'in' 
    required : Bool 
    schema   : Base 
```

### 3.2 Path Templates
Represents structured API routes such as `/todos/{id}`.
Each path is composed of segments, which can be either literal strings or parameter placeholders.
This corresponds to the keys defined under `paths:` in OpenAPI.

```agda
data PathSegment : Set where
  lit   : String → PathSegment -- e.g., "todos"
  param : String → PathSegment -- e.g., "{id}"

record Path : Set where
  field
    segments : List PathSegment
```

For example, an OpenAPI path like "/todos/{id}" is represented as:

```code
PathTodos : Path
PathTodos =  record { segments = lit "todos" :: param "id" :: [] }
```

### 3.3 Request Bodies
Represents the payload sent with an HTTP request. Only certain methods can include a body.  
We restrict this directly at the type level to ensure REST correctness.

```agda
data Body : Method → Set where
  NoBody   : Body GET
  NoBodyD  : Body DELETE
  HasBody  : Schema → Body POST
  HasBodyU : Schema → Body PUT
  HasBodyP : Schema → Body PATCH
```

This guarantees that:
- `GET` and `DELETE` operations cannot define a request body
- `POST`, `PUT` and `PATCH` operations must include one, described by a `Schema`

### 3.4 Responses
Represents the possible responses returned by an endpoint.  
Each response pairs an HTTP status with a payload schema, corresponding directly to the `responses:` section in OpenAPI.

```agda
data Response : Set where
  response : Status → Schema → Response
```

A list of `Response` values defines the complete response mapping for an operation.

### 3.5 Endpoint
Describes a single REST operation, combining its path, method, parameters, request body, and responses.  
This corresponds directly to an OpenAPI operation object such as `get`, `post`, or `put`.


```agda
record Endpoint : Set where
  field
    route       : Path          
    method      : Method
    parameters  : List Parameter
    body        : Body method
    responses   : List Response
```

Together, endpoints form the operational core of the API specification.

---

## 4. API Level
Defines the top-level structure of an API specification.  
This corresponds to the root of an OpenAPI document, combining reusable schemas and all defined paths.

```agda
record API : Set where
  field  
    paths      : List Endpoint           -- all defined path operations
    components : List (String × Schema)  -- components/schemas
```

