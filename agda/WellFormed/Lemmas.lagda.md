# Well-Formedness Lemmas

This module contains a small collection of proof-oriented results that support the transition from syntax to semantics.

The `WellFormed` module defines the judgements (`WFSchema`, `WFParameter`, `WFPath`, `WFEndpoint`, `WFAPI`) that characterise structurally meaningful API specifications. From this point onward, semantic interpretation is defined **only** for specifications equipped with well-formedness proofs.

We do not attempt to enumerate all consequences of well-formedness here. Instead, semantic definitions proceed by *structural recursion* on well-formedness proofs, making ill-formed cases unrepresentable by construction. The lemmas included in this module are therefore intentionally representative rather than exhaustive: they illustrate how well-formedness eliminates impossible configurations and enforces coherence between independently specified components.

The lemmas are organised into two complementary groups:

- **Inversion lemmas**, which extract structural facts from well-formedness proofs and justify total semantic definitions.
- **Coherence lemmas**, which establish consistency between independently specified components and rule out misalignment. 

```agda
module WellFormed.Lemmas where

open import Prelude
open import Syntax.Syntax
open import WellFormed.Core
```

## 1. Inversion Lemmas for Totality

Once later definitions are restricted to well-formed specifications, we repeatedly want to recover the structural facts that well-formedness guarantees. In practice, this is done by pattern matching on well-formedness derivations or by using small “inversion” lemmas like the ones below.

These lemmas justify total semantic definitions by eliminating impossible cases. In particular, we focus on inversion lemmas for `WFSchema`, since schema structure is the primary source of partiality in later definitions. Other well-formedness judgements are consumed directly by pattern matching at their point of use.

### 1.1 Arrays have an item schema

Array schemas are the simplest source of partiality in our schema model: an array type is only meaningful if an element schema is present. While the syntax allows the `items` field to be absent, well-formedness rules this out for array schemas.

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
array-inv (wf-object tyObj _ _ _ _ _) tyArr =
  ⊥-elim (object≢array (trans (sym tyObj) tyArr))

-- Primitive schemas cannot have array type.
array-inv (wf-prim primTy _ _ _) tyArr =
  ⊥-elim (prim-not-array (subst IsPrimitive tyArr primTy))
```

This lemma ensures that semantic interpretations of arrays never need to handle a missing `items` case. Recursive definitions on array schemas are therefore total once well-formedness is assumed.

### 1.2 Object schemas have coherent fields

Object schemas are the most structurally rich case in our subset: they carry named properties and a list of required fields that must be scoped to those properties. Later semantic and compatibility definitions rely on these invariants when interpreting or comparing object-shaped payloads.

The following inversion lemma extracts the exact guarantees provided by well-formedness for object schemas: object schemas have no array items, all property schemas are themselves well-formed, and every required field name corresponds to a declared property key. Additionally, object schemas have unique property keys and a duplicate-free `required` list, so `properties` behaves like a finite map (unique keys), and `required` behaves like a finite set (no duplicates), rather than order-sensitive lists.

```agda
record ObjectInv (s : Schema) : Set where
  field
    noItems : Schema.items s ≡ nothing
    propsWF : All WFSchema (values (Schema.properties s))
    reqWF   : All (λ r → r ∈ keys (Schema.properties s)) (Schema.required s)
    uniqKeys : Unique (keys (Schema.properties s))
    uniqReq  : Unique (Schema.required s)

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
object-inv (wf-object _ noItems propsWF reqWF uniqK uniqR) _ =
  record
    { noItems  = noItems
    ; propsWF  = propsWF
    ; reqWF    = reqWF
    ; uniqKeys = uniqK
    ; uniqReq  = uniqR 
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
wfpath-placeholders-declared (wf-path _ ⊆l _) x∈ =
  All-∈ ⊆l x∈

wfpath-pathparams-mentioned :
  ∀ {p ps x}
  → WFPath p ps
  → x ∈ pathParamNames ps
  → x ∈ pathPlaceholders p
wfpath-pathparams-mentioned (wf-path _ _ ⊆r) x∈ =
  All-∈ ⊆r x∈
```

Together, these lemmas ensure that parameter interpretation is consistent under well-formed endpoints: every placeholder corresponds to a declared path parameter, and no declared path parameter is unused.
