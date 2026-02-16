# API Refinement Properties

Having defined API refinement, we now establish its basic algebraic structure.

As with schema and endpoint refinement, the goal is to show that API refinement forms a preorder:

- Reflexivity: every well-formed API safely refines itself.
- Transitivity: safe API evolutions compose.

These properties justify treating API refinement as a principled notion of backwards-compatible evolution. In particular, they ensure that compatibility is stable under multi-step version changes.

All proofs proceed structurally, lifting the corresponding results from schema and endpoint refinement to the API level.

```agda
module Semantics.APIRefinementProperties where

open import Prelude
open import Syntax.Syntax

open import WellFormed.Core

open import Semantics.SchemaRefinement
open import Semantics.SchemaRefinementProperties

open import Semantics.EndpointRefinement
open import Semantics.EndpointRefinementProperties

open import Semantics.APIRefinement

open Σ using (fst ; snd)
```

---

## 1. Reflexivity

Every well-formed API safely refines itself.

Reflexivity follows structurally from reflexivity of schema and endpoint refinement. We first establish reflexivity for component lists and endpoint lists, then combine them into the main API-level result.

---

### 1.1 Component reflexivity

Component refinement iterates over the old component list and aligns entries via lookup. Reflexivity therefore follows by recursion over the list, using `⊑Co-refl` for schemas.

```agda
Components⊑-weaken :
    ∀ {k s cs new}
  → k ∉ keys cs
  → Components⊑ cs new
  → Components⊑ cs ((k , s) :: new)

Components⊑-weaken {cs = []} _ tt = tt

Components⊑-weaken
  {k} {s} {cs = (k' , s') :: cs'} {new}
  (notin::_ k≢k' k∉tail)
  ( (t , (lkt , r)) , rest )
  =
  ( t , (lookupComponent-there k≢k' lkt , r) )
  , Components⊑-weaken k∉tail rest
```

```agda
Components⊑-refl :
  ∀ {cs}
  → Unique (keys cs)
  → All WFSchema (values cs)
  → Components⊑ cs cs

Components⊑-refl {cs = []} _ _ = tt

Components⊑-refl
  {cs = (k , s) :: cs'}
  (uniq::_ k∉tail uniqTail)
  (all::_ wfS wfTail)
  =
  ( s , (lookupComponent-here , ⊑Co-refl wfS) )
  , Components⊑-weaken
      k∉tail
      (Components⊑-refl uniqTail wfTail)
```

---

### 1.2 Endpoint Reflexivity

Endpoint list refinement mirrors the component case.
We prove reflexivity by recursion over the endpoint list, using `Endpoint⊑-refl` and a weakening lemma to skip fresh heads during lookup.

```agda
Endpoints⊑-weaken :
    ∀ {e es new}
  → (Endpoint.route e , Endpoint.method e) ∉ endpointKeys es
  → Endpoints⊑ es new
  → Endpoints⊑ es (e :: new)

Endpoints⊑-weaken {es = []} _ tt = tt
Endpoints⊑-weaken
  {e} {es = h :: es'} {new}
  (notin::_ head≢ tail∉)
  ( (e' , (lk , r)) , rest )
  =
  ( e' , (lookupEndpoint-there head≢ lk , r) )
  , Endpoints⊑-weaken tail∉ rest
```

```agda
Endpoints⊑-refl :
  ∀ {es}
  → Unique (endpointKeys es)
  → All WFEndpoint es
  → Endpoints⊑ es es

Endpoints⊑-refl {es = []} _ _ = tt
Endpoints⊑-refl
  {es = e :: es'}
  (uniq::_ e∉tail uniqTail)
  (all::_ wfE wfTail)
  =
  ( e , (lookupEndpoint-here , Endpoint⊑-refl wfE) )
  , Endpoints⊑-weaken
      e∉tail
      (Endpoints⊑-refl uniqTail wfTail)
```

---

### 1.3 API Reflexivity

API refinement is reflexive when both component and endpoint refinement are reflexive.

```agda
API⊑-refl :
  ∀ {a}
  → WFAPI a
  → API⊑ a a

API⊑-refl
  {a}
  (wf-api wfComps uniqComps wfPaths uniqPaths)
  =
  ⊑-api
    (wf-api wfComps uniqComps wfPaths uniqPaths)
    (wf-api wfComps uniqComps wfPaths uniqPaths)
    (Components⊑-refl uniqComps wfComps)
    (Endpoints⊑-refl uniqPaths wfPaths)
```

---


