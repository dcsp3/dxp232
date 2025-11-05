# Minimal Syntax
This module defines a minimal version of the core syntax for our REST DSL.  
Each type represents a *syntactic category* of the language.

```agda
module MinimalSyntax where

open import Prelude
```

## 1. HTTP Methods
A minimal set of methods supported by our language

```agda
data Method : Set where
  GET  : Method
  POST : Method
```

## 2. HTTP Statuses
Status codes that an endpoint may respond with. (OK → 200, NotFound → 404)

```agda
data Status : Set where
  OK       : Status
  NotFound : Status
```

## 3. Payload Schemas
The "shape" of data exchanged in requests/responses.
Here we model only a minimal notion of data: each field is associated with a `Base` type symbol
(e.g. `int`, `string`).
Later, in the semantics, these base symbols can be interpreted as actual Agda types.

```agda 
data Base : Set where
  int    : Base
  string : Base

data Schema : Set where    
  object  : List (String × Base) → Schema 
```

For example, a todo schema could look like:

```agda
Todo : Schema
Todo = object (("id" , int) :: ("title" , string) :: [])
```

An error schema could look like:

```agda
Error : Schema
Error = object (("message" , string) :: [])
```

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

```agda
TodoEndpoint : Endpoint
TodoEndpoint = record
  { path      = "/todos/{id}"
  ; method    = GET
  ; body      = NoBody
  ; responses = (Case OK       Todo)
             :: (Case NotFound Error)
             :: []
  }
```

