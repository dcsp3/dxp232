# Older Naive Minimal Syntax
This module defines a minimal version of the core syntax for our REST DSL.  
Each type represents a *syntactic category* of the language.

```
module MinimalSyntax where

open import Prelude
```

## 1. HTTP Methods
A minimal set of methods supported by our language

```
data Method : Set where
  GET  : Method
  POST : Method
```

## 2. HTTP Statuses
Status codes that an endpoint may respond with. (OK → 200, NotFound → 404)

```
data Status : Set where
  OK       : Status
  NotFound : Status
```

## 3. Payload Schemas
The "shape" of data exchanged in requests/responses. These are synctactic, not Agda types, enabling reasoning about structure.
>This is where dependent reasoning about data shapes begins.

```
data Schema : Set where
  SInt     : Schema                            -- integers
  SString  : Schema                            -- strings
  SObject  : List (String × Schema) → Schema   -- object type (fields + sub-schemas)
```

For example, a todo schema could look like:

```
Todo : Schema
Todo = SObject (("id" , SInt) :: ("title" , SString) :: [])
```

An error schema could look like:

```
Error : Schema
Error = SObject (("message" , SString) :: [])
```

## 4. Request Bodies (Dependent on Method)
`Body` is indexed by the HTTP method, encoding REST rules in the type itself.

```
data Body : Method → Set where
  NoBody  : Body GET
  HasBody : Schema → Body POST
```

This ensures:
- `GET` requests cannot have a body
- `POST` requests must carry a payload defined by a `Schema`

Attempting to assign a body to `GET` will result in a **type error**; enforcing REST correctness at compile time.

## 5. Response Cases
Each response paris a status code with its payload schema

```
data RespCase : Set where
  Case : Status → Schema → RespCase
```

We represent endpoint responses as a *list* of `RespCase` values instead of a function `Status → Schema`.

## 6. Endpoint Specification
An `Endpoint` describes a single REST endpoint.

```
record Endpoint : Set where
  field
    path      : String        -- Route (e.g. "/todos/{id}")
    method    : Method        -- HTTP method
    body      : Body method   -- Request Body (dependent on method)
    responses : List RespCase -- Mapping of statuses to schemas
```

Example:

```
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
