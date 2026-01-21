# Well-Formedness Lemmas and Examples

This module contains a small collection of proof-oriented results that support the transition from syntax to semantics.

The `WellFormed` module defines the judgements (`WFSchema`, `WFParameter`, `WFPath`, `WFEndpoint`, `WFAPI`) that characterise structurally meaningful API specifications. From this point onward, semantic interpretation is defined **only** for specifications equipped with well-formedness proofs.

We do not attempt to enumerate all consequences of well-formedness here. Instead, semantic definitions proceed by *structural recursion* on well-formedness proofs, making ill-formed cases unrepresentable by construction. The lemmas included in this module are therefore intentionally representative rather than exhaustive: they illustrate how well-formedness eliminates impossible configurations and enforces coherence between independently specified components.

The lemmas are organised into two complementary groups:

- **Inversion lemmas**, which extract structural facts from well-formedness proofs and justify total semantic definitions.
- **Coherence lemmas**, which establish consistency between independently specified components and rule out misalignment. 

In addition, we include a complete well-formedness proof for the translated Todo API, which will serve as a running example throughout the remainder of the project.

```agda
module WellFormedExamples where

open import Prelude
open import Syntax
open import WellFormed
open import ExampleTodoAPI
```

## 1. Inversion Lemmas for Totality

Once later definitions are restricted to well-formed specifications, we repeatedly want to recover the structural facts that well-formedness guarantees. In practice, this is done by pattern matching on a well-formedness derivations or by using small “inversion” lemmas like the ones below.

These lemmas justify total semantic definitions by eliminating impossible cases. In particular, we focus on inversion lemmas for `WFSchema`, since schema structure is the primary source of partiality in later definitions. Other well-formedness judgements are consumed directly by pattern matching at their point of use.

### 1.1 Arrays have an item schema

Array schemas are the simplest source of partiality in the OpenAPI schema model: an array type is only meaningful if an element schema is present. While the syntax allows the `items` field to be absent, well-formedness rules this out for array schemas.

The following inversion lemma makes this guarantee explicit. It shows that for any well-formed schema whose type is `array`, an item schema must exist and is itself well-formed. This fact is later used to define array semantics and refinement relations by total recursion on the item schema.

```agda
record ArrayInv (s : Schema) : Set where
  field
    item   : Schema
    items≡ : Schema.items s ≡ just item
    wfItem : WFSchema item
    
object≢array : object ≡ array → ⊥
object≢array ()

prim-not-array : IsPrimitive array → ⊥
prim-not-array ()

array-inv : ∀ {s} → WFSchema s → Schema.type s ≡ array → ArrayInv s

-- Array case: the item schema and its well-formedness are already carried by the WF proof.
array-inv (wf-array _ items≡just wf-it _ _) _ =
  record
    { item   = _
    ; items≡ = items≡just
    ; wfItem = wf-it
    }

-- Object schemas cannot have array type.
array-inv (wf-object tyObj _ _ _) tyArr =
  ⊥-elim (object≢array (trans (sym tyObj) tyArr))

-- Primitive schemas cannot have array type.
array-inv (wf-prim primTy _ _ _) tyArr =
  ⊥-elim (prim-not-array (subst IsPrimitive tyArr primTy))
```

This lemma ensures that semantic interpretations of arrays never need to handle a missing `items` case. Recursive definitions on array schemas are therefore total once well-formedness is assumed.

### 1.2 Object schemas have coherent fields

Object schemas are the most structurally rich case in our subset: they carry named properties and a list of required fields that must be scoped to those properties. Later semantic and compatibility definitions rely on these invariants when interpreting or comparing object-shaped payloads.

The following inversion lemma extracts the exact guarantees provided by well-formedness for object schemas: object schemas have no array items, all property schemas are themselves well-formed, and every required field name corresponds to a declared property key.

```agda
record ObjectInv (s : Schema) : Set where
  field
    noItems : Schema.items s ≡ nothing
    propsWF : All (λ kv → WFSchema (snd kv)) (Schema.properties s)
    reqWF   : All (λ r → r ∈ keys (Schema.properties s)) (Schema.required s)

array≢object : array ≡ object → ⊥
array≢object ()

prim-not-object : IsPrimitive object → ⊥
prim-not-object ()

object-inv :
  ∀ {s}
  → WFSchema s
  → Schema.type s ≡ object
  → ObjectInv s

-- Object case: all coherence facts are carried by the WF proof.
object-inv (wf-object _ noItems propsWF reqWF) _ =
  record
    { noItems = noItems
    ; propsWF = propsWF
    ; reqWF   = reqWF
    }

-- Array schemas cannot have object type.
object-inv (wf-array tyArr _ _ _ _) tyObj =
  ⊥-elim (array≢object (trans (sym tyArr) tyObj))

-- Primitive schemas cannot have object type.
object-inv (wf-prim primTy _ _ _) tyObj =
  ⊥-elim (prim-not-object (subst IsPrimitive tyObj primTy))
```

This lemma justifies total semantic interpretations of object schemas: required-field access is safe, property schemas are well-formed, and no array-specific cases need to be considered.

Primitive schemas require no corresponding inversion lemma, since they carry no internal structure.

## 2. Coherence Lemmas for Safety

`WFPath p ps` connects a path template `p` and a parameter list `ps`, ruling out mismatches such as missing placeholders or orphan path parameters.

The following lemmas extract the two directions of correspondence guaranteed by `WFPath`. They make this invariant directly usable in later definitions, without pattern matching on well-formedness proofs.

```agda
wfpath-placeholders-declared :
  ∀ {p ps x}
  → WFPath p ps
  → x ∈ pathPlaceholders p
  → x ∈ pathParamNames ps
wfpath-placeholders-declared (wf-path ⊆l _) x∈ =
  All-∈ ⊆l x∈

wfpath-pathparams-mentioned :
  ∀ {p ps x}
  → WFPath p ps
  → x ∈ pathParamNames ps
  → x ∈ pathPlaceholders p
wfpath-pathparams-mentioned (wf-path _ ⊆r) x∈ =
  All-∈ ⊆r x∈
```

Together, these lemmas ensure that parameter interpretation is consistent under well-formed endpoints: every placeholder corresponds to a declared path parameter, and no declared path parameter is unused.

## 3. A Well-Formed Todo API

We conclude this module with a complete, explicit well-formedness proof for the translated Todo API. Unlike the previous sections, which focused on general-purpose lemmas, this section demonstrates how the well-formedness judgements are actually used to validate a concrete API specification.

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
