# Endpoint Refinement

Schema refinement gives us a notion of safe evolution at the level of data. Now we lift that idea to whole endpoints.

An endpoint is more than a schema: it has a route, a method, parameters, an optional request body, and a collection of responses. If we change any of these, we may change what clients can send or what they observe.

The key question is:

> When is a new endpoint a safe replacement for an old one?

The answer follows the same variance discipline we used earlier:

- Things the **server consumes** (parameters and request bodies) are checked
  **contravariantly**.
- Things the **client observes** (responses) are checked **covariantly**.
- The structural identity of the endpoint (route and method) must not change.

This file formalisese that judgement.

---

```agda
module Semantics.EndpointRefinement where

open import Prelude
open import Syntax
open import WellFormed.Core

open import Semantics.Variance
open import Semantics.SchemaRefinement

open Σ using (fst ; snd)
```

## 1. Endpoint refinement

At the top level we define a relation

```agda
Endpoint⊑ : Endpoint → Endpoint → Set
```

which should be read as:

>'eNew' safely refines 'eOld'.

Endpoint refinement needs two ingredients:

1. a variance-aware use of schema refinement (requests contra, responses co)
2. a way to align parameters and responses across two endpoints

For the second part we use simple lookup functions, and those require decidable
equality on `ParamLocation` and `Status`.

### 1.1 Decidable equality

```agda
ParamLocation≟ : (a b : ParamLocation) → Dec (a ≡ b)
ParamLocation≟ path  path  = yes refl
ParamLocation≟ query query = yes refl
ParamLocation≟ path  query = no (λ ())
ParamLocation≟ query path  = no (λ ())

Status≟ : (a b : Status) → Dec (a ≡ b)
Status≟ OK         OK         = yes refl
Status≟ NotFound   NotFound   = yes refl
Status≟ BadRequest BadRequest = yes refl
Status≟ NoContent  NoContent  = yes refl

Status≟ OK         NotFound   = no (λ ())
Status≟ OK         BadRequest = no (λ ())
Status≟ OK         NoContent  = no (λ ())

Status≟ NotFound   OK         = no (λ ())
Status≟ NotFound   BadRequest = no (λ ())
Status≟ NotFound   NoContent  = no (λ ())

Status≟ BadRequest OK         = no (λ ())
Status≟ BadRequest NotFound   = no (λ ())
Status≟ BadRequest NoContent  = no (λ ())

Status≟ NoContent  OK         = no (λ ())
Status≟ NoContent  NotFound   = no (λ ())
Status≟ NoContent  BadRequest = no (λ ())
```

### 1.2 Lookup helpers

We align list-based endpoint components by looking up corresponding entries.

Parameters are identified by their `(location , name)` pair.

```agda
lookupParam : ParamLocation → String → List Parameter → Maybe Parameter
lookupParam ℓ k [] = nothing
lookupParam ℓ k (p :: ps) with ParamLocation≟ ℓ (Parameter.location p)
... | no  _ = lookupParam ℓ k ps
... | yes _ with (k ≟ Parameter.name p)
...   | yes _ = just p
...   | no  _ = lookupParam ℓ k ps
```

Responses are identified by their status code.

```agda
lookupResp : Status → List Response → Maybe Schema
lookupResp st [] = nothing
lookupResp st (response st' s :: rs) with Status≟ st st'
... | yes _ = just s
... | no  _ = lookupResp st rs
```

As with schema refinement, endpoint refinement will be defined by matching components via lookup, then applying the relevant variance-aware schema check.

---

## 2. Component judgements
