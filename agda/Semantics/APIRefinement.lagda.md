# API Refinement

An API packages together all endpoints and reusable schemas that make up a specification.

We define API refinement structurally. An API refines another when:
- every declared component schema evolves safely, and
- every existing endpoint continues to behave safely under evolution.

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

Since APIs are collections rather than single objects, refinement is defined by alignment via keys:
- components are matched by their name,
- endpoints are matched by their route and method.

The definition lifts the refinement relations already established for schemas and endpoints to the top level.

## 1. Component Lookup

Component schemas are aligned by their declared name.

We therefore define lookup over the `components` list by matching on the component key (`String`). This mirrors the lookup functions used at lower layers and will be used to align component schemas across API versions.

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

Lookup will be used to align endpoints across API versions.
We now establish its basic structural properties.

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

## 3. Component Refinement

Components are aligned by name.
For each old component, the new API must provide a schema that refines it (covariantly). Extra components in the new API are allowed.

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

For each old endpoint, the new API must provide a matching endpoint that refines it. Extra endpoints in the new API are allowed.

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
