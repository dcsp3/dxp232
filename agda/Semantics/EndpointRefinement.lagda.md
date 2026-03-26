# Endpoint Refinement

Schema refinement gives us a notion of safe evolution at the level of data. Now we lift that idea to whole endpoints.

An endpoint has a route, a method, parameters, an optional request body, and a collection of responses. The variance discipline follows schema refinement:

- Things the **server consumes** (parameters and request bodies) are checked
  **contravariantly**.
- Things the **client observes** (responses) are checked **covariantly**.
- The structural identity of the endpoint (route and method) must not change.

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

`Endpoint⊑ eOld eNew` means 'eNew' safely refines 'eOld'.

We only relate well-formed endpoints. The well-formedness invariant ensures that parameter keys and response status codes are unique, so the lookup-based definitions below are unambiguous.

### 1.1 Lookup helpers

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
```

```agda
-- Skip a head parameter whose (location,name) cannot match (ℓ,k)
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
lookupParam→∈ :
  ∀ {ℓ k p ps}
  → lookupParam ℓ k ps ≡ just p
  → (ℓ , k) ∈ paramKeys ps

lookupParam→∈ {ps = []} ()

lookupParam→∈ {ℓ} {k} {p} {q :: qs} lk
  with ParamLocation≟ ℓ (Parameter.location q)
... | no _ =
      there (lookupParam→∈ lk)

... | yes refl
  with k ≟ Parameter.name q
...   | no _ =
        there (lookupParam→∈ lk)

...   | yes refl =
        here
```

```agda
lookupParam-∉-nothing :
    ∀ {ℓ k ps}
  → (ℓ , k) ∉ paramKeys ps
  → lookupParam ℓ k ps ≡ nothing

lookupParam-∉-nothing {ℓ} {k} {[]} _ = refl

lookupParam-∉-nothing {ℓ} {k} {p :: ps} (notin::_ head≢ tail∉)
  with ParamLocation≟ ℓ (Parameter.location p)
... | no  _ = lookupParam-∉-nothing tail∉
... | yes refl
  with k ≟ Parameter.name p
... | no  _ = lookupParam-∉-nothing tail∉
... | yes refl = ⊥-elim (head≢ refl)
```

```agda
lookupParam-location :
  ∀ {ℓ k ps p}
  → lookupParam ℓ k ps ≡ just p
  → Parameter.location p ≡ ℓ
lookupParam-location {ℓ} {k} {[]} ()
lookupParam-location {ℓ} {k} {h :: ps} lk
  with ParamLocation≟ ℓ (Parameter.location h)
... | no  _    = lookupParam-location {ps = ps} lk
... | yes refl
  with k ≟ Parameter.name h
... | no  _    = lookupParam-location {ps = ps} lk
... | yes refl = subst (λ x → Parameter.location x ≡ ℓ) (just-inj lk) refl
```

```agda
lookupParam-name :
  ∀ {ℓ k ps p}
  → lookupParam ℓ k ps ≡ just p
  → Parameter.name p ≡ k
lookupParam-name {ℓ} {k} {[]} ()
lookupParam-name {ℓ} {k} {h :: ps} lk
  with ParamLocation≟ ℓ (Parameter.location h)
... | no  _    = lookupParam-name {ps = ps} lk
... | yes refl
  with k ≟ Parameter.name h
... | no  _    = lookupParam-name {ps = ps} lk
... | yes refl = subst (λ x → Parameter.name x ≡ k) (just-inj lk) refl
```

```agda
lookupParam-key :
  ∀ {p q new}
  → lookupParam (Parameter.location p) (Parameter.name p) new ≡ just q
  → lookupParam (Parameter.location q) (Parameter.name q) new ≡ just q
lookupParam-key {p} {q} {new} lkeq =
  subst
    (λ ℓ → lookupParam ℓ (Parameter.name q) new ≡ just q)
    (sym (lookupParam-location
            {ℓ = Parameter.location p}
            {k = Parameter.name p}
            {ps = new}
            {p = q}
            lkeq))
    (subst
       (λ k → lookupParam (Parameter.location p) k new ≡ just q)
       (sym (lookupParam-name
               {ℓ = Parameter.location p}
               {k = Parameter.name p}
               {ps = new}
               {p = q}
               lkeq))
       lkeq)
```

```agda
lookupParam-self :
  ∀ {ℓ k p ps}
  → lookupParam ℓ k ps ≡ just p
  → lookupParam (Parameter.location p) (Parameter.name p) ps ≡ just p
lookupParam-self {ℓ} {k} {p} {ps} lk =
  subst (λ ℓ' → lookupParam ℓ' (Parameter.name p) ps ≡ just p)
        (sym (lookupParam-location {ps = ps} lk))
        (subst (λ k' → lookupParam ℓ k' ps ≡ just p)
               (sym (lookupParam-name {ps = ps} lk))
               lk)
```

```agda
-- Strip an optional head parameter from a lookup that finds a required parameter
lookupParam-strip :
  ∀ {ℓ k p h rest}
  → Parameter.required h ≡ false
  → lookupParam ℓ k (h :: rest) ≡ just p
  → Parameter.required p ≡ true
  → lookupParam ℓ k rest ≡ just p
lookupParam-strip {ℓ} {k} {p} {h} {rest} hReq lk req
  with ParamLocation≟ ℓ (Parameter.location h)
... | no _ = lk
... | yes refl
  with k ≟ Parameter.name h
... | no _ = lk
... | yes refl =
      ⊥-elim
        (false≢true
          (trans
            (trans (sym hReq) (cong Parameter.required (just-inj lk)))
            req))
```

```agda
lookupResp-here :
  ∀ {st s rs}
  → lookupResp st (response st s :: rs) ≡ just s
lookupResp-here {st} {s} {rs}
  with Status≟ st st | Status≟-refl {st}
... | yes refl | refl = refl

-- Skip a head response whose status cannot match the one we are looking up
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

```agda
lookupResp-wf :
    ∀ {st t} {rs : List Response}
  → All WFResponse rs
  → lookupResp st rs ≡ just t
  → WFSchema t
lookupResp-wf {st} {rs = response st' s :: rs} (all::_ (wf-response wfS) rest) lk
  with Status≟ st st'
... | no  _    = lookupResp-wf rest lk
... | yes refl = subst WFSchema (just-inj lk) wfS
lookupResp-wf {rs = []} all[] ()
```

```agda
lookupResp→∈ :
  ∀ {st s rs}
  → lookupResp st rs ≡ just s
  → st ∈ respKeys rs
lookupResp→∈ {st} {rs = response st' s :: rs} lk
  with Status≟ st st'
... | yes refl = here
... | no  _    = there (lookupResp→∈ lk)
lookupResp→∈ {rs = []} ()
```

---

## 2. Component judgements

Endpoint refinement is built out of three smaller relations: parameter refinement, body refinement, and response refinement.

### 2.1 Parameters

Since parameters are consumed by the server, they are checked contravariantly. The new endpoint must accept at least what the old one did, and must not introduce new required parameters.

```agda
ReqWeakens : Bool → Bool → Set
ReqWeakens old new = new ≡ true → old ≡ true

Param⊑Contra : Parameter → Parameter → Set
Param⊑Contra pOld pNew =
    Parameter.location pOld ≡ Parameter.location pNew
  × Parameter.name     pOld ≡ Parameter.name     pNew
  × Parameter.schema   pOld ≡ Parameter.schema   pNew
  × ReqWeakens (Parameter.required pOld) (Parameter.required pNew)
```

```agda
OldParamsPreserved : List Parameter → List Parameter → Set
OldParamsPreserved [] new = ⊤
OldParamsPreserved (p :: ps) new =
  (Σ Parameter (λ p' →
       lookupParam (Parameter.location p) (Parameter.name p) new ≡ just p'
     × Param⊑Contra p p'))
  × OldParamsPreserved ps new

NewRequiredSafe : List Parameter → List Parameter → Set
NewRequiredSafe old new =
  ∀ {ℓ k p}
  → lookupParam ℓ k new ≡ just p
  → Parameter.required p ≡ true
  → Σ Parameter (λ pOld →
       lookupParam ℓ k old ≡ just pOld
     × Parameter.required pOld ≡ true)
```

```agda
Params⊑Contra : List Parameter → List Parameter → Set
Params⊑Contra old new =
    OldParamsPreserved old new
  × NewRequiredSafe old new
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

Endpoint refinement pins the route and method, then combines the three component checks.

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
