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
data IsPrimitive : Base → Set where
  prim-integer : IsPrimitive integer
  prim-string  : IsPrimitive string
  prim-boolean : IsPrimitive boolean
  prim-number  : IsPrimitive number

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

## 2. Well-formed Parameters

Parameters represent values passed through the URL path or query string.
Our syntax permits constructing arbitrary `Parameter` records, but not every such record corresponds to a structurally meaningful OpenAPI-style parameter in our subset.

There are two structural constraints we enforce:

1. **Path parameters are required.**  
   A path template cannot omit a placeholder segment, so OpenAPI treats path parameters as required.

2. **Parameters are restricted to primitive base types in this DSL.**  
   Although OpenAPI supports array/object parameters, doing so relies on additional machinery (a full schema shape for the parameter plus serialization controls such as `style` and `explode`). Our `Parameter` syntax records only a base type (`Base`), so allowing `array` or `object` here would be underspecified. We therefore restrict parameters to primitive base types in this fragment.

The judgement `WFParameter p` enforces only these structural invariants.

```agda
data WFParameter : Parameter → Set where

  wf-path-param :
    ∀ {p}
    → Parameter.location p ≡ path
    → Parameter.required p ≡ true
    → IsPrimitive (Parameter.schema p)
    → WFParameter p

  wf-query-param :
    ∀ {p}
    → Parameter.location p ≡ query
    → IsPrimitive (Parameter.schema p)
    → WFParameter p
```

## 3. Well-formed Paths

In our DSL, a `Path` is a structured template made of `PathSegment`s, where segments are either literals (`lit "todos"`) or placeholders (`param "id"`). This corresponds to OpenAPI-style route templates such as `/todos/{id}`.

Since paths and parameters are specified independently in the syntax, it is possible to construct inconsistent specifications. For example, a path may contain a placeholder `{id}` without any corresponding path parameter declaration, or a path parameter may be declared without appearing in the path template.

The judgement `WFPath path params` enforces structural coherence between a path template and the list of parameters declared for an operation. It enforces the following two constraints:

1. **Every placeholder is declared**: for each `{x}` appearing in the path, there is a parameter with `location = path` and `name = x`.
2. **No orphan path parameters**: every parameter declared with `location = path` appears as a placeholder `{x}` in the path.

These two directions ensure the path template and its declared path parameters describe the same set of path variables. This mirrors the OpenAPI requirement that template expressions in a path MUST correspond to declared `in: path` parameters of the same name.

>This judgement does not enforce parameter typing (handled by `WFParameter`) and does not impose best practices or behavioural routing properties. It exists solely to rule out structurally incoherent path/parameter combinations before semantics and compatibility reasoning.

```agda
sameLoc : ParamLocation → ParamLocation → Bool
sameLoc path  path  = true
sameLoc path  query = false
sameLoc query path  = false
sameLoc query query = true

pathPlaceholders : Path → List String
pathPlaceholders p = go (Path.segments p)
  where
    go : List PathSegment → List String
    go [] = []
    go (lit _   :: ss) = go ss
    go (param x :: ss) = x :: go ss

paramNamesAt : ParamLocation → List Parameter → List String
paramNamesAt ℓ [] = []
paramNamesAt ℓ (p :: ps) =
  if sameLoc ℓ (Parameter.location p)
  then Parameter.name p :: paramNamesAt ℓ ps
  else paramNamesAt ℓ ps

pathParamNames : List Parameter → List String
pathParamNames = paramNamesAt path

data WFPath : Path → List Parameter → Set where
  wf-path :
      ∀ {p ps}
    → pathPlaceholders p ⊆ pathParamNames ps
    → pathParamNames ps ⊆ pathPlaceholders p
    → WFPath p ps
```

## 4. Well-formed Request Bodies

The type `Body : Method → Set` already enforces a key structural constraint: only methods that admit a request body can carry one (and methods like `GET` cannot). This prevents method/body mismatches by construction.

However, the `Body` type does not ensure that the schema attached to a request body is itself structurally coherent. The judgement `WFBody b` therefore propagates schema well-formedness upward:

- `NoBody` is always well-formed.
- `HasBody s` is well-formed precisely when `WFSchema s` holds.

```agda
data WFBody : ∀ {m} → Body m → Set where
  wf-nobody   : WFBody NoBody
  wf-nobodyD  : WFBody NoBodyD

  wf-hasBody  : ∀ {s} → WFSchema s → WFBody (HasBody  s)
  wf-hasBodyU : ∀ {s} → WFSchema s → WFBody (HasBodyU s)
  wf-hasBodyP : ∀ {s} → WFSchema s → WFBody (HasBodyP s)
```

## 5. Well-formed Responses

A response associates a status code with a schema describing the response payload. While the syntax allows any schema to be attached to a response, well-formedness ensures that the attached schema is structurally coherent.

The judgement `WFResponse r` enforces this minimal invariant: the response schema must be well-formed (`WFSchema`).

```agda
data WFResponse : Response → Set where
  wf-response :
    ∀ {st s}
    → WFSchema s
    → WFResponse (response st s)
```

## 6. Well-formed Endpoints

An `Endpoint` bundles together the operational parts of a REST operation: its route, method, parameters, request body, and responses.

Individually, each piece can be syntactically valid while still being structurally incoherent as an operation (e.g. route placeholders not matching declared path parameters, malformed body schema, malformed response schemas).

The judgement `WFEndpoint e` states that an endpoint is structurally coherent when:
- its path template and declared parameters agree (`WFPath`)
- each declared parameter is structurally valid (`WFParameter`)
- its request body (if present by method) carries a well-formed schema (`WFBody`)
- each response carries a well-formed schema (`WFResponse`)

```agda
data WFEndpoint : Endpoint → Set where
  wf-endpoint :
    ∀ {e}
    → WFPath (Endpoint.route e) (Endpoint.parameters e)
    → All WFParameter (Endpoint.parameters e)
    → WFBody (Endpoint.body e)
    → All WFResponse (Endpoint.responses e)
    → WFEndpoint e
```

## 7. Well-formed APIs

An `API` specification bundles together reusable component schemas and the collection of defined path operations. Well-formedness at the API level is compositional: an API is well-formed when all of its component schemas are well-formed and all of its paths (endpoints) are well-formed.

```agda
data WFAPI : API → Set where
  wf-api :
    ∀ {api}
    → All (λ kv → WFSchema (snd kv)) (API.components api)
    → All WFEndpoint (API.paths api)
    → WFAPI api
```

---

Well-formedness serves as the boundary between raw syntax and meaningful specifications. This allows us to restrict all semantic definitions to well-formed APs from this point onward.

To support this transition, the [`WellFormedExamples.lagda.md`]() module introduces a small number of representative inversion and coherence lemmas, together with a complete well-formedness proof for the Todo API example. These results are demonstrations of how the judgements defined above are intended to be used in practice.
