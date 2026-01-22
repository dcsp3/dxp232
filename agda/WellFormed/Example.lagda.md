# Well-Formedness Example

```agda
module WellFormed.Example where

open import Prelude
open import Syntax
open import WellFormed.Core
open import ExampleTodoAPI
```

## A Well-Formed Todo API

This module gives a complete, explicit well-formedness proof for the translated Todo API. We demonstrate how the well-formedness judgements are actually used to validate a concrete API specification.

The proof is written compositionally, following the structure of the API:

1. component schemas,
2. endpoint fragments (paths, parameters, bodies, responses),
3. the full API.

### 3.1 Component Schemas

We begin by establishing well-formedness for the schemas appearing in the Todo API components section.

**Primitive schemas**
```agda
wf-IdSchema : WFSchema IdSchema
wf-IdSchema =
  wf-prim prim-integer refl refl refl

wf-TitleSchema : WFSchema TitleSchema
wf-TitleSchema =
  wf-prim prim-string refl refl refl

wf-MessageSchema : WFSchema MessageSchema
wf-MessageSchema =
  wf-prim prim-string refl refl refl
```

These schemas are well-formed by construction and carry no object or array specific structure.

**Object schemas**
```agda
Todo-is-object : Schema.type Todo ≡ object
Todo-is-object = refl

Todo-has-no-items : Schema.items Todo ≡ nothing
Todo-has-no-items = refl

Error-is-object : Schema.type Error ≡ object
Error-is-object = refl

Error-has-no-items : Schema.items Error ≡ nothing
Error-has-no-items = refl

wf-TodoSchema : WFSchema Todo
wf-TodoSchema =
  wf-object
    Todo-is-object
    Todo-has-no-items
    Todo-props-wf
    Todo-required-ok
  where
    Todo-props-wf :
      All (λ kv → WFSchema (snd kv)) (Schema.properties Todo)
    Todo-props-wf =
      all::_ wf-IdSchema
        (all::_ wf-TitleSchema all[])

    Todo-required-ok :
      All (λ r → r ∈ keys (Schema.properties Todo)) (Schema.required Todo)
    Todo-required-ok =
      all::_ here
        (all::_ (there here) all[])

wf-ErrorSchema : WFSchema Error
wf-ErrorSchema =
  wf-object
    Error-is-object
    Error-has-no-items
    Error-props-wf
    Error-required-ok
  where
    Error-props-wf :
      All (λ kv → WFSchema (snd kv)) (Schema.properties Error)
    Error-props-wf =
      all::_ wf-MessageSchema all[]

    Error-required-ok :
      All (λ r → r ∈ keys (Schema.properties Error)) (Schema.required Error)
    Error-required-ok =
      all::_ here all[]
```

These proofs rely directly on the wf-object constructor and make explicit:

- the object shape,
- the absence of array items,
- recursive well-formedness of property schemas,
- coherence of required fields.

### 3.2 Endpoint Fragments

We now establish well-formedness for the pieces that make up a Todo endpoint.

**Path parameter**

```agda
wf-ParamId : WFParameter ParamId
wf-ParamId = wf-path-param refl refl prim-integer
```

This ensures that the parameter is:
- located in the path,
- marked as required,
- primitive-typed.

**Path coherence**

```agda
wf-PathTodos : WFPath PathTodos (ParamId :: [])
wf-PathTodos =
  wf-path
    (all::_ here all[])
    (all::_ here all[])
```

This establishes the exact correspondence between:
- placeholders appearing in the path template, and
- declared path parameters.

**Request body**

```agda
wf-BodyGetTodo : WFBody NoBody
wf-BodyGetTodo = wf-nobody
```

The GET endpoint carries no request body, which is always well-formed.

**Responses**

```agda
wf-RespOK : WFResponse (response OK Todo)
wf-RespOK =
  wf-response wf-TodoSchema

wf-RespNotFound : WFResponse (response NotFound Error)
wf-RespNotFound =
  wf-response wf-ErrorSchema
```

Each response propagates schema well-formedness upward.

**Endpoint Assembly**

```agda
wf-GetTodoEndpoint : WFEndpoint GetTodoEndpoint
wf-GetTodoEndpoint =
  wf-endpoint
    wf-PathTodos
    (all::_ wf-ParamId all[])
    wf-BodyGetTodo
    (all::_ wf-RespOK
      (all::_ wf-RespNotFound all[]))
```

This endpoint proof is entirely compositional: no global reasoning is required.

### 3.3 Whole API

Finally, the full API is well-formed once all component schemas and endpoints are.

```agda
wf-TodoAPI : WFAPI TodoAPI
wf-TodoAPI =
  wf-api
    wf-components
    (all::_ wf-GetTodoEndpoint all[])
  where
    wf-components :
      All (λ kv → WFSchema (snd kv)) (API.components TodoAPI)
    wf-components =
      all::_ wf-TodoSchema
        (all::_ wf-ErrorSchema all[])
```

This witness will be reused throughout the remainder of the project. In particular:
- all semantic interpretations are defined only for APIs equipped with WFAPI,
- compatibility and refinement relations assume well-formedness implicitly,
- drift results will be instantiated using this concrete example.
