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

This file formalises that judgement.

---

```agda
module Semantics.EndpointRefinement where

open import Prelude
open import Syntax.Syntax
open import Syntax.Decidable

open import WellFormed.Core

open import Semantics.Variance
open import Semantics.SchemaRefinement

open Σ using (fst ; snd)
```

## 1. Endpoint refinement

At the top level we define a relation `Endpoint⊑ : Endpoint → Endpoint → Set` where:

> `Endpoint⊑ eOld eNew` means 'eNew' safely refines 'eOld'.

Endpoint refinement needs two things:

1. a variance-aware use of schema refinement (requests contra, responses co)
2. a way to align parameters and responses across two endpoints

For the second part we use simple lookup functions, using decidable
equalities on `ParamLocation` and `Status`.

As with schema refinement, we only relate well-formed endpoints. The
well-formedness invariant ensures that parameter keys and response status
codes are unique, so that the lookup-based definitions below are unambiguous.

### 1.1 Lookup helpers

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

---

### 1.2 Lookup computation lemmas


The refinement relations below use lookup to align list-based components.
To make the properties proofs go through, we record the two basic lookup
facts we will use repeatedly:

- **here**: looking up the head key succeeds immediately
- **there**: if the head key does not match, lookup proceeds into the tail

```agda
lookupParam-here :
  ∀ {p ps}
  → lookupParam
       (Parameter.location p)
       (Parameter.name p)
       (p :: ps)
    ≡ just p
lookupParam-here {p} {ps}
  with ParamLocation≟ (Parameter.location p) (Parameter.location p)
... | no  contra = ⊥-elim (contra refl)
... | yes refl
  with (Parameter.name p ≟ Parameter.name p)
... | yes refl = refl
... | no  contra = ⊥-elim (contra refl)

-- skip a head parameter whose (location,name) cannot match (ℓ,k)
lookupParam-there :
    ∀ {h ℓ k ps p}
  → (Parameter.location h , Parameter.name h) ≢ (ℓ , k)
  → lookupParam ℓ k ps ≡ just p
  → lookupParam ℓ k (h :: ps) ≡ just p
lookupParam-there {h} {ℓ} {k} {ps} {p} head≢ ih
  with ParamLocation≟ ℓ (Parameter.location h)
... | no _ = ih
... | yes refl
  with (k ≟ Parameter.name h)
...   | no _ = ih
...   | yes refl = ⊥-elim (head≢ refl)
```

```agda
lookupResp-here :
  ∀ {st s rs}
  → lookupResp st (response st s :: rs) ≡ just s
lookupResp-here {st} {s} {rs}
  with Status≟ st st | Status≟-refl {st}
... | yes refl | refl = refl

-- skip a head response whose status cannot match the one we are looking up
lookupResp-there :
    ∀ {st st₀ s₀ rs t}
  → st₀ ≢ st
  → lookupResp st rs ≡ just t
  → lookupResp st (response st₀ s₀ :: rs) ≡ just t
lookupResp-there {st} {st₀} {s₀} {rs} {t} st₀≢st ih
  with Status≟ st st₀
... | yes st≡st₀ = ⊥-elim (st₀≢st (sym st≡st₀))
... | no  _      = ih
```

Endpoint refinement will be defined by matching components via lookup, then applying the relevant variance-aware schema check, similar to schema refinement.

---

## 2. Component judgements

Endpoint refinement is built out of three smaller relations:

- parameter refinement (request-facing, so contravariant)
- body refinement (request-facing, so contravariant)
- response refinement (client-observed, so covariant)

We define these first, then combine them into the main endpoint judgement.

### 2.1 Parameters

A parameter is identified by its `(location , name)` pair.
The new endpoint must still provide every parameter that old clients may send.

Since parameters in our syntax carry a `Base` schema, we require the base type
to be unchanged. We also forbid parameters from becoming newly required.

```agda
ReqWeakens : Bool → Bool → Set
ReqWeakens old new = new ≡ true → old ≡ true

Param⊑Contra : Parameter → Parameter → Set
Param⊑Contra pOld pNew =
    Parameter.location pOld ≡ Parameter.location pNew
  × Parameter.name     pOld ≡ Parameter.name     pNew
  × Parameter.schema   pOld ≡ Parameter.schema   pNew
  × ReqWeakens (Parameter.required pOld) (Parameter.required pNew)

Params⊑Contra : List Parameter → List Parameter → Set
Params⊑Contra [] new = ⊤
Params⊑Contra (p :: ps) new =
  (Σ Parameter (λ p' →
       lookupParam (Parameter.location p) (Parameter.name p) new ≡ just p'
     × Param⊑Contra p p'))
  × Params⊑Contra ps new
```

---

### 2.2 Request bodies

Bodies are checked contravariantly using the variance wrapper around schema refinement.

```agda
Body⊑Contra : ∀ {m n} → m ≡ n → Body m → Body n → Set
Body⊑Contra {GET}    {GET}    refl NoBody       NoBody       = ⊤
Body⊑Contra {DELETE} {DELETE} refl NoBodyD      NoBodyD      = ⊤
Body⊑Contra {POST}   {POST}   refl (HasBody  s) (HasBody  t) = Schema⊑ Contra s t
Body⊑Contra {PUT}    {PUT}    refl (HasBodyU s) (HasBodyU t) = Schema⊑ Contra s t
Body⊑Contra {PATCH}  {PATCH}  refl (HasBodyP s) (HasBodyP t) = Schema⊑ Contra s t
```

---

### 2.3 Responses

Responses are checked covariantly.
For each status code present in the old endpoint, the new endpoint must still
provide a schema for that status, and it must refine the old schema.

```agda
Resps⊑Co : List Response → List Response → Set
Resps⊑Co [] new = ⊤
Resps⊑Co (response st s :: rs) new =
  (Σ Schema (λ t →
       lookupResp st new ≡ just t
     × Schema⊑ Co s t))
  × Resps⊑Co rs new
```

---

### 2.4 Endpoint refinement

Finally, endpoint refinement pins the structural identity of the endpoint (route and method)
and then combines the three component checks.

```agda
data Endpoint⊑ : Endpoint → Endpoint → Set where
  ⊑-endpoint :
      ∀ {eOld eNew}
      → WFEndpoint eOld
      → WFEndpoint eNew
      → Endpoint.route  eOld ≡ Endpoint.route  eNew
      → (method≡ : Endpoint.method eOld ≡ Endpoint.method eNew)
      → Params⊑Contra
          (Endpoint.parameters eOld)
          (Endpoint.parameters eNew)
      → Body⊑Contra method≡
          (Endpoint.body eOld)
          (Endpoint.body eNew)
      → Resps⊑Co
          (Endpoint.responses eOld)
          (Endpoint.responses eNew)
      → Endpoint⊑ eOld eNew
```

