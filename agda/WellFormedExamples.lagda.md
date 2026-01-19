# Well-Formedness Lemmas and Examples

This module contains a small collection of proof-oriented results that support the transition from syntax to semantics.

The `WellFormed` module defines the judgements (`WFSchema`, `WFParameter`, `WFPath`, `WFEndpoint`, `WFAPI`) that characterise structurally meaningful API specifications. From this point onward, semantic interpretation is defined **only** for specifications equipped with well-formedness proofs.

We do not attempt to enumerate all consequences of well-formedness here. Instead, semantic definitions proceed by *structural recursion* on well-formedness proofs, making ill-formed cases unrepresentable by construction. The lemmas included in this module are therefore intentionally representative rather than exhaustive: they illustrate how well-formedness eliminates impossible configurations and enforces coherence between independently specified components.

In addition, we include a complete well-formedness proof for the translated Todo API, which will serve as a running example throughout the remainder of the project.

```agda
module WellFormedExamples where

open import Prelude
open import Syntax
open import WellFormed
open import ExampleTodoAPI
```

## 1. Inversion and Safety Lemmas (for Totality)

Once later definitions are restricted to well-formed specifications, we repeatedly want to recover the structural facts that well-formedness guarantees. In practice, this is done by pattern matching on a well-formedness derivation (or by using small “inversion” lemmas like the ones below).

These lemmas are not intended to be deep results in their own right. Rather, they exemplify how well-formedness proofs are used: by extracting exactly the invariants needed to define subsequent layers without partiality or hidden assumptions.

In particular, we focus inversion lemmas on `WFSchema`, since schema structure is the primary source of partiality in later definitions. Other well-formedness judgements (parameters, bodies, endpoints, APIs) are consumed directly by pattern matching at the point of use and do not require separate inversion lemmas.

Primitive schemas are intentionally omitted from this section because they have no internal structure, and their well-formedness is already a complete description of their shape.

### 1.1 Arrays have an item schema

Array schemas are the simplest source of partiality in the OpenAPI schema model: an array type is only meaningful if an element schema is present. While the syntax allows the `items` field to be absent, well-formedness rules this out for array schemas.

The following inversion lemma makes this guarantee explicit. It shows that for any well-formed schema whose type is `array`, an item schema must exist and is itself well-formed.

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

Later semantic and compatibility definitions recurse over schemas by structural recursion on `WFSchema`. In the array case, this lemma allows recursion on the element schema without introducing a partial “missing items” branch.

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

This lemma supports total interpretation and comparison of object schemas by ensuring that property access and required-field reasoning never encounter ill-scoped or structurally inconsistent cases.
