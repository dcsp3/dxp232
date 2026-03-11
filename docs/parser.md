# Parser Layer

The aim of the parser layer is to bridge real OpenAPI specifications and the formal DSL defined in our Agda development.

All refinement and compatibility results in this project are stated over values of type API in the DSL. However, users write OpenAPI YAML. The parser is responsible for translating OpenAPI documents into a canonical DSL abstract syntax tree (AST), which can then be checked for results such as:

- Well-formedness
- Endpoint/API Refinement
- Compatibilty and Drift

In other words, the parser is the user-facing entry point that allows the formal theory to be applied to real API specifications. 

---

## Design

The parser is intentionally fragment-restricted.

It does not attempt to support the full OpenAPI 3.1 specification. Instead, it extracts the subset of OpenAPI that is representable in the DSL. Any unsupported features are rejected early.

This ensures:

- Every translated specification inhabits the DSL.
- No invalid or partial DSL terms are constructed.
- Formal checks operate on well-defined inputs.

The parser enforces fragment boundaries, while deeper structural guarantees (such as well-formedness proofs and refinement properties) are handled in Agda.

---

## Translation Pipeline

### 1. YAML Loading

The OpenAPI document are parsed using a safe YAML loader. Basic structural checks ensure that required top-level fields (e.g. `openapi`, `paths`) are present.

---

### 2. Schema Translation

Schemas defined under `components.schemas` are translated recursively into DSL `Schema` values.

Supported features:

- Primitive base types (`integer`, `string`, `boolean`)
- Object schemas with properties and required fields
- Array schemas with `items`
- `$ref` references to `#/components/schemas/...`

Unsupported features (rejected):

- `oneOf`, `allOf`, `anyOf`
- Polymorphism constructs
- Non-JSON content
- Arbitrary `$ref` targets

The DSL does not model schema references directly, so referenced schemas are inlined during translation.

---

### 3. Path Translation

Each OpenAPI path string (e.g. `/todos/{id}`) is decomposed into DSL `PathSegment`s:

- Literal segments (`lit`)
- Parameter segments (`param`)

Only standard path parameter syntax is supported.

---

### 4. Operation Translation

For each path and supported HTTP method, an `Endpoint` is constructed.

This includes:

- Method mapping
- Parameter translation (path and query only)
- Request body translation (for `POST`, `PUT`, `PATCH`)
- Response translation with status mapping

Unsupported constructs (rejected):

- Path-level parameters
- Non-JSON request/response content
- Unsupported status codes
- Non-primitive parameter types

---

### 5. API Construction

Finally, all translated endpoints and component schemas are assembled into a DSL `API` value.

This value is the canonical representation used by the formal refinement layer.

---

## Intended Usage

The parser is designed to be part of an automated compatibility pipeline:

1. Parse OpenAPI YAML → DSL `API`
2. Check well-formedness
3. Check refinement (and/or equivalence)
4. Return structured compatibility results

This design supports a future frontend interface where users can paste two OpenAPI specifications and receive a precise compatibility verdict derived from the formal refinement theory.

---

## Scope and Limitations

The parser is deliberately conservative. It does not aim to be a general-purpose OpenAPI validator. Instead, it defines a precise, well-behaved fragment aligned with the formal model.

Specifications outside this fragment are rejected with explicit error messages.

This keeps the boundary between implementation and formal reasoning clear:

- The parser extracts a DSL-representable fragment.
- Agda proves properties about the extracted representation.