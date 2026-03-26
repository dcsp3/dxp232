# API Refinement

An API consists of the endpoints and reusable component schemas that make up a specification.

We define API refinement structurally. A new API refines an old one when:
- every declared component schema evolves safely, and
- every existing endpoint is preserved with compatible behaviour.

```agda
module Semantics.APIRefinement where

open import Prelude
open import Syntax.Syntax
open import Syntax.Decidable

open import WellFormed.Core

open import Semantics.Variance
open import Semantics.SchemaRefinement
open import Semantics.EndpointRefinement

open Σ using (fst ; snd)
```

Since APIs are collections rather than single values, refinement is defined by matching entries by key:
- components are matched by name,
- endpoints are matched by route and method.

## 1. Component Lookup

Component schemas are aligned by their declared name.

```agda
lookupComponent :
  String → List (String × Schema) → Maybe Schema

lookupComponent k [] = nothing

lookupComponent k ((k' , s) :: cs)
  with k ≟ k'
... | yes _ = just s
... | no  _ = lookupComponent k cs
```

---

### 1.1 Lookup of the head element

If we search for the key at the head of the list, lookup succeeds immediately.

```agda
lookupComponent-here :
  ∀ {k s cs}
  → lookupComponent k ((k , s) :: cs) ≡ just s

lookupComponent-here {k} {s} {cs}
  with k ≟ k
... | yes _  = refl
... | no neq = ⊥-elim (neq refl)
```

---

### 1.2 Lookup past a different head

If the head key does not match the one we are searching for, lookup proceeds into the tail.

```agda
lookupComponent-there :
    ∀ {k k₀ s₀ cs t}
  → k₀ ≢ k
  → lookupComponent k cs ≡ just t
  → lookupComponent k ((k₀ , s₀) :: cs) ≡ just t

lookupComponent-there {k} {k₀} {s₀} {cs} {t} k₀≢k ih
  with k ≟ k₀
... | yes k≡k₀ = ⊥-elim (k₀≢k (sym k≡k₀))
... | no  _    = ih
```

---

### 1.3 Successful lookup implies key membership

If lookup succeeds, the key must appear in the component list.

```agda
lookupComponent→∈ :
  ∀ {k s cs}
  → lookupComponent k cs ≡ just s
  → k ∈ keys cs
  
lookupComponent→∈ {k} {cs = (k' , s') :: cs} lk
  with k ≟ k'
... | yes refl = here
... | no  _    = there (lookupComponent→∈ lk)
lookupComponent→∈ {cs = []} ()
```

---

## 2. Endpoint Lookup

To define refinement over lists of endpoints, we first define lookup by `(route , method)`.

```agda
lookupEndpoint :
  Path → Method → List Endpoint → Maybe Endpoint

lookupEndpoint r m [] = nothing

lookupEndpoint r m (e :: es)
  with Path≟ r (Endpoint.route e)
... | no _ = lookupEndpoint r m es
... | yes _
  with Method≟ m (Endpoint.method e)
...   | no _ = lookupEndpoint r m es
...   | yes _ = just e
```

---

### 2.1 Lookup of the head element

If we search for the route and method of the head element, lookup returns that element.

```agda
lookupEndpoint-here :
  ∀ {e es}
  → lookupEndpoint
       (Endpoint.route e)
       (Endpoint.method e)
       (e :: es)
    ≡ just e

lookupEndpoint-here {e} {es}
  with Path≟ (Endpoint.route e) (Endpoint.route e)
... | no neq = ⊥-elim (neq refl)
... | yes _
  with Method≟ (Endpoint.method e) (Endpoint.method e)
...   | no neq = ⊥-elim (neq refl)
...   | yes _  = refl
```

---

### 2.2 Lookup past a different head

If either the route or the method does not match, lookup proceeds to the tail.

```agda
lookupEndpoint-there :
    ∀ {h r m es e}
  → (Endpoint.route h , Endpoint.method h)
      ≢ (r , m)
  → lookupEndpoint r m es ≡ just e
  → lookupEndpoint r m (h :: es) ≡ just e

lookupEndpoint-there {h} {r} {m} {es} {e} head≢ ih
  with Path≟ r (Endpoint.route h)
... | no _ = ih
... | yes refl
  with Method≟ m (Endpoint.method h)
...   | no _ = ih
...   | yes refl = ⊥-elim (head≢ refl)
```

---

### 2.3 Successful lookup implies key membership

If lookup succeeds, the `(route, method)` pair must appear in the endpoint key list.

```agda
lookupEndpoint→∈ :
  ∀ {r m e es}
  → lookupEndpoint r m es ≡ just e
  → (r , m) ∈ endpointKeys es
  
lookupEndpoint→∈ {r} {m} {es = e :: es} lk
  with Path≟ r (Endpoint.route e)
... | no  _    = there (lookupEndpoint→∈ lk)
... | yes refl
  with Method≟ m (Endpoint.method e)
... | no  _    = there (lookupEndpoint→∈ lk)
... | yes refl = here
lookupEndpoint→∈ {es = []} ()
```

---

## 3. Component Refinement

```agda
Components⊑ :
  List (String × Schema)
  → List (String × Schema)
  → Set

Components⊑ [] new = ⊤

Components⊑ ((k , s) :: cs) new =
  (Σ Schema (λ t →
       lookupComponent k new ≡ just t
     × Schema⊑ Co s t))
  × Components⊑ cs new
```

---

## 4. Endpoint List Refinement

```agda
Endpoints⊑ :
  List Endpoint
  → List Endpoint
  → Set

Endpoints⊑ [] new = ⊤

Endpoints⊑ (e :: es) new =
  (Σ Endpoint (λ e' →
       lookupEndpoint
         (Endpoint.route e)
         (Endpoint.method e)
         new ≡ just e'
     × Endpoint⊑ e e'))
  × Endpoints⊑ es new
```

---

## 5. API Refinement

An API `aNew` safely refines `aOld` when:

- both APIs are well-formed,
- all old components are preserved and refined,
- all old endpoints are preserved and refined.

```agda
data API⊑ : API → API → Set where
  ⊑-api :
      ∀ {aOld aNew}
      → WFAPI aOld
      → WFAPI aNew
      → Components⊑
          (API.components aOld)
          (API.components aNew)
      → Endpoints⊑
          (API.paths aOld)
          (API.paths aNew)
      → API⊑ aOld aNew
```
