# API Refinement

An API packages together all endpoints and reusable schemas that make up a specification.

We define API refinement structurally. An API refines another when:
- every existing endpoint continues to behave safely under evolution, and
- every declared component schema evolves safely.

```agda
module Semantics.APIRefinement where

open import Prelude
open import Syntax.Syntax
open import Syntax.Decidable

open import WellFormed.Core

open import Semantics.SchemaRefinement
open import Semantics.EndpointRefinement

open Σ using (fst ; snd)
```

Since APIs are collections rather than single objects, refinement is defined by alignment via keys:
- endpoints are matched by their route and method,
- components are matched by their name.

The definition lifts the refinement relations already established for schemas and endpoints to the top level.

---

## 1. Endpoint Lookup

To define refinement over lists of endpoints, we first define lookup by `(route , method)`.

This mirrors the lookup functions used for parameters and responses in the lower layers.

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

### 1.1 Lookup of the head element

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

### 1.2 Lookup past a different head

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
