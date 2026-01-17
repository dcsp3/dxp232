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

