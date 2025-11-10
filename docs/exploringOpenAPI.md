# Exploring the OpenAPI Specification

The aim of this document is to explore how I can formalise the OpenAPI Specification (OAS) to design my DSL for REST APIs. While OpenAPI provides a detailed and standardised description of API structures, it does not capture their *meaning*. There is no way to reason about whether two endpoints are compatible, equivalent, or safely evolvable; and this gap often leads to API drift: when a client and server slowly diverge in behaviour despite sharing the same structural specification.

This document identifies the key components of OpenAPI relevant to my project, outlines how they can be represented in my typed DSL, and explore how I could extend OpenAPI's descriptive power by layering formal semantics on top. The goal is to use OpenAPI as the structural foundation and build a semantic layer that detects and prevents API drift.

---

## Background

### What OpenAPI Is

OpenAPI is the most widely used specification for describing RESTful APIs. It defines a structured, language-agnostic format for documenting endpoints, HTTP methods, input/output data models, and associated metadata. The specification uses YAML or JSON and integrates with JSON Schema to describe data types and constraints.

An OpenAPI document is intended to serve as a contract between client and server. It provides a shared understanding of available operations and their expected request and response formats.

### Why It Matters for This Project

To formally represent APIs in a type-theoretic setting, I first need a clear view of how OpenAPI organises information:

- How endpoints are defined and grouped under paths.
- How operations (like GET and POST) specify request and response data.
- How schemas (using JSON Schema) describe the shape of exchanged data.

Understanding this structure will allow my DSL to directly represent OpenAPI documents, essentially treating each DSL construct as a formal equivalent of an OpenAPI concept.

### The Gap

OpenAPI defines what an API looks like, not what it means. For instance:

- Two schemas may differ syntactically but still describe the same data.
- A change might be backward compatible in practice but appear incompatible in structure.
- Nothing in the spec enforces behavioural consistency between versions.

I want to close this gap by expressing these relationships explicitly and prove when drift has or hasn’t occurred.

### Formalising a Subset

The full OpenAPI 3.1 specification is large and complex, supporting advanced features like callbacks, polymorphism, multiple media types, and recursive `$ref` definitions. To make formalisation tractable, I will initially focus on a smaller but representative subset, one that captures the typical structure of REST APIs without unnecessary detail. This can later be extended as the DSL evolves.

The goal is to model core properties like:
- Paths and their operations (GET and POST)
- Parameters (path and query)
- Request bodies (JSON only)
- Responses (status-to-schema mappings)
- Schemas (objects, primitives, optional fields)

This subset reflects the core of REST API design while remaining manageable to encode precisely in a typed language.

---

## The Structure of OpenAPI (v3.1)

An OpenAPI document is a [hierarchical structure](#example-minimal-openapi-spec) consisting of several major components:

- **Info**: Metadata such as title, version, and description.
- **Servers**: The environments or base URLs where the API can be accessed.
- **Paths**: The set of API endpoints and their supported operations.
- **Components**: Reusable schemas, parameters, and examples.

For the purpose of formalisation, the `paths` and `components` sections are the most relevant, as they define the operational and data-level aspects of the API.

### 1. Paths and Operations

Each path (for example, `/todos/{id}`) can contain one or more operations, each representing an HTTP method such as GET or POST. Each operation in turn defines:

* Parameters (where they occur, e.g., path or query)
* Request body (if any)
* Responses (mapping of status codes to data schemas) 

### 2. Parameters

Parameters define inputs that can modify or specify an operation’s behaviour. OpenAPI supports parameters in four locations: `path`, `query`, `header`, and `cookie`. For my subset, only `path` and `query` parameters are required.

Each parameter has:

- `name`: identifier
- `in`: location (e.g., path or query)
- `required`: whether it must be provided
- `schema`: its type and format

These can be represented as a list of parameter definitions within the DSL.

### 3. Request Body

In OpenAPI, the `requestBody` field describes the content a client sends with an operation such as POST or PUT. It can specify multiple content types and schemas. To simplify, I will limit this to a single media type: `application/json`. This allows a direct mapping between the request body and a single schema definition in the DSL.

### 4. Responses

Each operation specifies a `responses` object mapping status codes (like 200, 400, 404) to response definitions. Each response includes content types and associated schemas.

This can be represented as a list of response cases, pairing each status with the schema of its response body. This representation makes explicit the structural correspondence between status codes and expected data.

### 5. Schemas (JSON Schema Integration)

OpenAPI 3.1 integrates fully with JSON Schema (2020-12). Schemas describe the shape of the data exchanged between client and server using constructs such as:

- `type`: basic kind (`object`, `string`, `integer`, etc.)
- `properties`: fields of an object
- `required`: list of mandatory fields
- `items`: schema of array elements

In the formalisation, only finite schemas built from primitive and flat object types are included. This ensures decidable type checking and simplifies correspondence proofs between request/response data and endpoint specifications.

---

## Choosing a Subset to Formalise 

Below is a proposed subset of OpenAPI features chosen for formalisation. These are expressive enough to represent real APIs yet simple enough to verify and manipulate within a dependently typed system.


| Category | Feature | Included? | Rationale |
|-----------|----------|-----------|-----------|
| **HTTP Methods** | GET, POST, PUT, DELETE, PATCH | ✅ | Covers the standard REST operations, allowing a fuller representation of CRUD patterns. |
| **Paths** | Path templates like `/todos/{id}` | ✅ | Core routing mechanism; enables parameterised endpoints. |
| **Parameters** | Path and Query | ✅ | Capture primary forms of endpoint input. |
| **Request Body** | JSON content only | ✅ | Restricting to JSON simplifies model while matching common practice. |
| **Responses** | 200 (OK), 404 (Not Found), 400 (Bad Request), 204 (No Content) | ✅ | Represents typical success and error cases with minimal overhead. |
| **Schema Types** | `object`, `string`, `integer`, `boolean`, `array` | ✅ | Adds flexibility for list-based responses and request collections. |
| **Optional Fields** | via `required` property | ✅ | Captures partial or extensible data models. |
| **Default Values** | Basic scalar defaults | ✅ | Enhances expressivity for simple cases. |
| **Enumerations** | Fixed sets of allowed strings or numbers | ✅ | Common in OpenAPI and straightforward to model. |
| **Examples and Descriptions** | Optional metadata fields | ✅ | Adds documentation richness without semantic weight. |
| **References (`$ref`)** | |  ❌ | Adds complexity via recursion and indirection; deferred to later stages. |
| **Compositions (`oneOf`, `allOf`, `anyOf`)** | | ❌ | Hard to represent formally; excluded for tractability. |
| **Authentication and Servers** | | ❌ | Contextual rather than structural. |
| **Headers and Cookies** |  | ❌ | Peripheral; excluded to focus on path-level definitions. |


This subset forms a minimal formal core of OpenAPI sufficient to represent typical REST APIs. It includes all constructs needed to describe endpoints, their inputs, and outputs, while excluding features that complicate formal reasoning without contributing to structure. Each construct in this subset will be represented directly in the DSL’s syntax, providing a one-to-one correspondence with its OpenAPI counterpart. Future extensions (like `$ref` and authentication) can build on this foundation once the base representation is complete.

With this, I conclude the structural exploration of OpenAPI. The next stage will focus on giving this structure formal meaning within the DSL.

---

## References

1. https://swagger.io/specification/
2. https://swagger.io/docs/specification/v3_0/about/
3. https://www.emergentmind.com/topics/openapi-specifications

---

## Appendix: Example Minimal OpenAPI Spec

```yaml
openapi: 3.1.0
info:
  title: Todo API
  version: "1.0"
paths:
  /todos/{id}:
    get:
      parameters:
        - name: id
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