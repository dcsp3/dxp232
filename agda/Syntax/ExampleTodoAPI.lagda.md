# Example Todo API

In this module we provide an example representation for a minimal OpenAPI 3.1 Todo API spec into our DSL's syntax (defined in [`Syntax.lagda.md`](./Syntax.lagda.md)).

```agda
module Syntax.ExampleTodoAPI where

open import Prelude
open import Syntax.Syntax
```

---

## Reference OpenAPI Specification

```yaml
openapi: 3.1.0
info:
  title: Todo API
  version: "1.0"
paths:
  /todos/{id}:
    get:
      parameters:
          name: id
          in: path
          required: true
          schema:
            type: integer
      responses:
        "200":
          content:
            application/json:
              schema:
                $ref: "#/components/schemas/Todo"
        "404":
          content:
            application/json:
              schema:
                $ref: "#/components/schemas/Error"
components:
  schemas:
    Todo:
      type: object
      properties:
        id: { type: integer }
        title: { type: string }
      required: [id, title]
    Error:
      type: object
      properties:
        message: { type: string }
      required: [message]
```

---

## Schemas

### Primitive Schemas

```agda
IdSchema : Schema
IdSchema = record { type = integer
                  ; properties = []
                  ; required = []
                  ; items = nothing
                  }

TitleSchema : Schema
TitleSchema = record { type = string
                     ; properties = []
                     ; required = []
                     ; items = nothing
                     }

MessageSchema : Schema
MessageSchema = record { type = string
                       ; properties = []
                       ; required = []
                       ; items = nothing
                       }
```



### Object Schemas

```agda
Todo : Schema
Todo = record
  { type        = object
  ; properties  = ("id" , IdSchema) :: ("title" , TitleSchema)  :: []
  ; required    = "id" :: "title" :: []
  ; items       = nothing
  }

Error : Schema
Error = record
  { type        = object
  ; properties  = ("message" , MessageSchema) :: []
  ; required    = "message" :: []
  ; items       = nothing
  }  
```

---

## Path

```agda
PathTodos : Path
PathTodos = record { segments = lit "todos" :: param "id" :: [] }
```

---


## Parameter

```agda
ParamId : Parameter
ParamId = record
  { name      = "id"
  ; location  = path
  ; required  = true
  ; schema    = integer
  }
```

---

## Responses

```agda
ResponsesGetTodo : List Response
ResponsesGetTodo = response OK Todo :: response NotFound Error :: []
```

---

## Endpoint

```agda
GetTodoEndpoint : Endpoint
GetTodoEndpoint = record
  { route       = PathTodos
  ; method      = GET
  ; parameters  = ParamId :: []
  ; body        = NoBody
  ; responses   = ResponsesGetTodo
  }
```

---

## API

```agda
TodoAPI : API
TodoAPI = record
  { paths = GetTodoEndpoint :: []
  ; components = ("Todo" , Todo) :: ("Error", Error) :: []
  }
```
