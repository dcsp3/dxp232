# Decidable Refinement

Given two well-formed specs, we either build a refinement proof or point to exactly what broke. Refinement and drift are two sides of the same coin.

We work bottom-up: decide schema refinement first, then lift to endpoints (checking parameters, bodies, responses), then lift again to full APIs (aligning components and endpoints via lookup). At each level, we return either a proof (`inl`) or a drift witness (`inr`) explaining the specific failure.

Well-formedness is critical here: it guarantees unique keys, making all lookups deterministic.

```agda
module Semantics.DecidableRefinement where

open import Prelude
open import Syntax.Syntax
open import Syntax.Decidable

open import WellFormed.Core

open import Semantics.Variance

open import Semantics.SchemaRefinement
open import Semantics.SchemaRefinementProperties

open import Semantics.EndpointRefinement
open import Semantics.APIRefinement

open import Semantics.Drift

open Σ using (fst ; snd)
```

## 1. Schema Refinement

Schemas refine covariantly. We recurse on shape: primitives check type equality, arrays recurse on item schemas, objects check properties and required-field subsets.

### 1.1 Property Refinement

For objects, we walk the old properties and check that each one exists in the new schema with a covariant refinement. Failures get recorded as `PropertyFailure`, which we later convert to `SchemaDrift`.

### Helpers

```agda
-- Property refinement can fail two ways:
data PropertyFailure
  (ps qs : List (String × Schema)) : Set where

  MissingProperty :  -- property was removed
      (k : String)
    → lookupProp k ps ≢ nothing
    → lookupProp k qs ≡ nothing
    → PropertyFailure ps qs

  NestedDrift :  -- property's schema drifted
      (k : String)
      (si ti : Schema)
    → lookupProp k ps ≡ just si
    → lookupProp k qs ≡ just ti
    → SchemaDrift si ti
    → PropertyFailure ps qs
```

```agda
liftPropertyFailure : ∀ {k s ps qs} → k ∉ keys ps → PropertyFailure ps qs → PropertyFailure ((k , s) :: ps) qs
liftPropertyFailure {k} k∉ (MissingProperty k' notNoth missing)
  with k' ≟ k
... | no  k'≢k = MissingProperty k' (λ contra → notNoth (trans (sym (lookupProp-skip k'≢k)) contra)) missing
... | yes refl = ⊥-elim (notNoth (lookupProp-∉-nothing k∉))
liftPropertyFailure {k} k∉ (NestedDrift k' si ti lkPs lkQt d)
  with k' ≟ k
... | no  k'≢k = NestedDrift k' si ti (trans (lookupProp-skip k'≢k) lkPs) lkQt d
... | yes refl = ⊥-elim (just≢nothing (trans (sym lkPs) (lookupProp-∉-nothing k∉)))
```

```agda
propertyFailure→SchemaDrift :
 ∀ {s t}
  → Schema.type s ≡ object
  → Schema.type t ≡ object
  → PropertyFailure (Schema.properties s)
                    (Schema.properties t)
  → SchemaDrift s t

propertyFailure→SchemaDrift {s} {t} tyS tyT
  (MissingProperty k notNoth missing) =
    PropertyRemoved tyS tyT notNoth missing

propertyFailure→SchemaDrift tyS tyT
  (NestedDrift k si ti lkPs lkQt d) =
    PropertyDrift tyS tyT lkPs lkQt d
```

### Decision

These are mutually recursive: property refinement needs schema checks, and schema refinement needs property checks for the object case.

```agda
mutual
  PropsRefine? :
      (ps qs : List (String × Schema))
    → All WFSchema (values ps)
    → All WFSchema (values qs)
    → Unique (keys ps)
    → PropsRefine Schema⊑Co ps qs
      ∔ PropertyFailure ps qs

  PropsRefine? [] qs _ _ _ = inl tt

  PropsRefine? ((k , s) :: ps) qs (all::_ wfS wfRest) wfQs (uniq::_ k∉tail uniqTail)
    with lookupProp k qs in eq

  -- Property missing in new schema
  ... | nothing =
        inr (MissingProperty k (λ contra → just≢nothing (trans (sym (lookupProp-here {k})) contra)) eq)

  -- Property exists
  ... | just t
    with Schema⊑Co? wfS (lookupProp-wf wfQs eq)
    
  -- Nested schema drift
  ... | inr d =
        inr (NestedDrift k s t (lookupProp-here {k}) eq d)

  -- Nested refinement succeeds → recurse
  ... | inl r
    with PropsRefine? ps qs wfRest wfQs uniqTail

  -- Tail failure propagates
  ... | inr pf =
        inr (liftPropertyFailure k∉tail pf)

  -- Everything succeeds
  ... | inl rest =
        inl ((t , (refl , r)) , rest)
```

```agda
  Schema⊑Co? :
    ∀ {s t}
    → WFSchema s
    → WFSchema t
    → Schema⊑Co s t ∔ SchemaDrift s t

  -- Primitives: check type equality
  Schema⊑Co? {s} {t}
    wfS@(wf-prim primS _ _ _)
    wfT@(wf-prim primT _ _ _)
    with Base≟ (Schema.type s) (Schema.type t)
  ... | yes refl =
        inl (⊑-prim wfS wfT primS primT refl)

  ... | no neq =
        inr (PrimitiveChanged primS primT neq)

  -- Arrays: recurse on item schema
  Schema⊑Co? {s} {t}
    wfS@(wf-array tyS itemsS wfItemS _ _)
    wfT@(wf-array tyT itemsT wfItemT _ _)
    with Schema⊑Co? wfItemS wfItemT
  ... | inl r =
        inl (⊑-array wfS wfT tyS tyT itemsS itemsT r)

  ... | inr d =
        inr (ArrayItemDrift tyS tyT itemsS itemsT d)

  -- Objects: property refinement + required field subset
  Schema⊑Co? {s} {t}
    wfS@(wf-object tyS _ wfPropsS wfReqS uniqS reqUniqS)
    wfT@(wf-object tyT _ wfPropsT wfReqT uniqT reqUniqT)
    with PropsRefine?
           (Schema.properties s)
           (Schema.properties t)
           wfPropsS
           wfPropsT
           uniqS
  ... | inr pf =
        inr (propertyFailure→SchemaDrift tyS tyT pf)

  ... | inl pr
    with Schema.required s ⊆? Schema.required t
  ...   | no subFail =
          let (k , (k∈ , k∉)) = ⊆-counterexample subFail
          in inr (RequiredFieldRemoved tyS tyT k∈ k∉)

  ...   | yes sub =
          inl (⊑-object wfS wfT tyS tyT pr sub)

  -- Shape mismatches: primitive ↔ array, primitive ↔ object, array ↔ object
  Schema⊑Co? (wf-prim primS _ _ _) (wf-array tyT _ _ _ _) =
    inr (ShapeMismatch (λ eq → prim≢array (subst IsPrimitive (trans eq tyT) primS)))

  Schema⊑Co? (wf-prim primS _ _ _) (wf-object tyT _ _ _ _ _) =
    inr (ShapeMismatch (λ eq → prim≢object (subst IsPrimitive (trans eq tyT) primS)))

  Schema⊑Co? (wf-array tyS _ _ _ _) (wf-prim primT _ _ _) =
    inr (ShapeMismatch (λ eq → prim≢array (subst IsPrimitive (trans (sym eq) tyS ) primT)))

  Schema⊑Co? (wf-array tyS _ _ _ _) (wf-object tyT _ _ _ _ _) =
    inr (ShapeMismatch (λ eq → array≢object (trans (sym tyS) (trans eq tyT))))

  Schema⊑Co? (wf-object tyS _ _ _ _ _) (wf-prim primT _ _ _) =
    inr (ShapeMismatch (λ eq → prim≢object (subst IsPrimitive (trans (sym eq) tyS) primT)))

  Schema⊑Co? (wf-object tyS _ _ _ _ _) (wf-array tyT _ _ _ _) =
    inr (ShapeMismatch (λ eq → array≢object (trans (sym tyT) (trans (sym eq) tyS))))
```

---

## 2. Endpoint Refinement

Endpoints decompose into four independent checks: parameters (contravariant), request body (contravariant), responses (covariant), and route/method identity. Each check either succeeds with a proof or fails with a specific `EndpointDrift` constructor.

### 2.1 Parameter Refinement

Parameters are contravariant, so we run two checks:
- `OldParamsPreserved?`: every old parameter must survive into the new list with the same schema and without weakening the required flag
- `NewRequiredSafe?`: no brand-new required parameters (new optional parameters are fine, and upgrading optional→required is caught by the first check)

We then combine both witnesses via `Params⊑Contra?`.

### 2.1.1 `OldParamsPreserved?`

### Helpers

```agda
data ParamFailure (old new : List Parameter) : Set where

  ParamRemoved :
      (ℓ : ParamLocation) (k : String)
    → lookupParam ℓ k old ≢ nothing
    → lookupParam ℓ k new ≡ nothing
    → ParamFailure old new

  ParamSchemaChanged :
        (p₀ p₁ : Parameter)
      → Parameter.location p₀ ≡ Parameter.location p₁
      → Parameter.name p₀ ≡ Parameter.name p₁
      → lookupParam (Parameter.location p₀) (Parameter.name p₀) old ≡ just p₀
      → lookupParam (Parameter.location p₁) (Parameter.name p₁) new ≡ just p₁
      → Parameter.schema p₀ ≢ Parameter.schema p₁
      → ParamFailure old new

  RequiredParamAdded :
        (p₀ p₁ : Parameter)
      → Parameter.location p₀ ≡ Parameter.location p₁
      → Parameter.name p₀ ≡ Parameter.name p₁
      → lookupParam (Parameter.location p₀) (Parameter.name p₀) old ≡ just p₀
      → lookupParam (Parameter.location p₁) (Parameter.name p₁) new ≡ just p₁
      → Parameter.required p₀ ≡ false
      → Parameter.required p₁ ≡ true
      → ParamFailure old new
```

```agda
-- Lift a tail failure to the full list
liftParamFailure :
    ∀ {p ps new}
  → (Parameter.location p , Parameter.name p) ∉ paramKeys ps
  → ParamFailure ps new
  → ParamFailure (p :: ps) new

liftParamFailure {p} {ps} p∉ (ParamRemoved ℓ k notNoth missing) =
  ParamRemoved ℓ k notNoth' missing
  where

  notNoth' :
    lookupParam ℓ k (p :: ps) ≢ nothing

  notNoth' contra
    with ParamLocation≟ ℓ (Parameter.location p)
  ... | no _ =
        notNoth contra

  ... | yes refl
    with k ≟ Parameter.name p
  ...   | no _ =
          notNoth contra

  ...   | yes refl =
          notNoth (lookupParam-∉-nothing p∉)
    
liftParamFailure {p} {ps} p∉ (ParamSchemaChanged p₀ p₁ loc≡ name≡ lk₀ lk₁ sch≢) =
  ParamSchemaChanged p₀ p₁ loc≡ name≡
    (lookupParam-there
      (λ eq → ∉-elim p∉ (subst (λ x → x ∈ paramKeys ps) (sym eq) (lookupParam→∈ lk₀)))
      lk₀)
    lk₁
    sch≢

liftParamFailure {p} {ps} p∉ (RequiredParamAdded p₀ p₁ loc≡ name≡ lk₀ lk₁ req₀ req₁) =
  RequiredParamAdded p₀ p₁ loc≡ name≡
    (lookupParam-there
      (λ eq → ∉-elim p∉ (subst (λ x → x ∈ paramKeys ps) (sym eq) (lookupParam→∈ lk₀)))
      lk₀)
    lk₁
    req₀
    req₁
```

```agda
-- Walk old params, look up each in new, check schema + required direction
OldParamsPreserved? :
  (old new : List Parameter)
  → Unique (paramKeys old)
  → OldParamsPreserved old new ∔ ParamFailure old new

OldParamsPreserved? [] new _ =
  inl tt

OldParamsPreserved? (p :: ps) new (uniq::_ p∉tail uniqTail)
  with lookupParam (Parameter.location p) (Parameter.name p) new in lkeq
... | nothing =
  inr (ParamRemoved
        (Parameter.location p)
        (Parameter.name p)
        (λ contra → just≢nothing (trans (sym (lookupParam-here {p} {ps})) contra))
        lkeq)

... | just q
  with Base≟ (Parameter.schema p) (Parameter.schema q)

-- schema mismatch
... | no sch≢ =
  inr (ParamSchemaChanged
        p q
        (sym (lookupParam-location {Parameter.location p} {Parameter.name p} {new} {q} lkeq))
        (sym (lookupParam-name {Parameter.location p} {Parameter.name p} {new} {q} lkeq))
        (lookupParam-here {p} {ps})
        (lookupParam-key {p} {q} {new} lkeq)
        sch≢)

-- schema matches
... | yes refl
  with Parameter.required p in reqP | Parameter.required q in reqQ

-- required strengthened
... | false | true =
  inr (RequiredParamAdded
        p q
        (sym (lookupParam-location {Parameter.location p} {Parameter.name p} {new} {q} lkeq))
        (sym (lookupParam-name     {Parameter.location p} {Parameter.name p} {new} {q} lkeq))
        (subst
           (λ r →
              lookupParam (Parameter.location p) (Parameter.name p)
                (record
                   { name     = Parameter.name p
                   ; location = Parameter.location p
                   ; required = r
                   ; schema   = Parameter.schema p
                   } :: ps)
              ≡ just p)
           reqP
           (lookupParam-here {p} {ps}))
        (lookupParam-key {p} {q} {new} lkeq)                               
        reqP
        reqQ)

-- safe cases → recurse

-- new param is not required (old may be either)
... | _ | false
  with OldParamsPreserved? ps new uniqTail
... | inl rest = inl ((q , (refl , (sym (lookupParam-location {Parameter.location p} {Parameter.name p} {new} {q} lkeq) , (sym (lookupParam-name {Parameter.location p} {Parameter.name p} {new} {q} lkeq) , (refl , (λ req≡true → ⊥-elim (false≢true (trans (sym reqQ) req≡true)))))))) , rest)
... | inr pf   = inr (liftParamFailure p∉tail pf)

OldParamsPreserved? (p :: ps) new (uniq::_ p∉tail uniqTail)
  | just q | yes refl | true | true
  with OldParamsPreserved? ps new uniqTail
... | inl rest = inl ((q , (refl , (sym (lookupParam-location {Parameter.location p} {Parameter.name p} {new} {q} lkeq) , (sym (lookupParam-name {Parameter.location p} {Parameter.name p} {new} {q}  lkeq) , (refl , ( λ _ → refl)))))) , rest)
... | inr pf   = inr (liftParamFailure p∉tail pf)
```

### 2.1.2 `NewRequiredSafe?`

```agda
-- Two ways new required parameters can break compatibility:
data NewRequiredFailure (old new : List Parameter) : Set where
  NewRequiredParam :  -- brand new required param
      (ℓ : ParamLocation) (k : String) (p : Parameter)
    → lookupParam ℓ k old ≡ nothing
    → lookupParam ℓ k new ≡ just p
    → Parameter.required p ≡ true
    → NewRequiredFailure old new

  NewRequiredOptionalInOld :
        (ℓ : ParamLocation) (k : String) (pOld p : Parameter)
      → lookupParam ℓ k old ≡ just pOld
      → lookupParam ℓ k new ≡ just p
      → Parameter.required pOld ≡ false
      → Parameter.required p ≡ true
      → NewRequiredFailure old new
```

```agda
-- Lift a tail failure to the full list
liftNewRequiredFailure :
  ∀ {old rest h}
  → (Parameter.location h , Parameter.name h) ∉ paramKeys rest
  → NewRequiredFailure old rest
  → NewRequiredFailure old (h :: rest)
  
liftNewRequiredFailure {h = h} h∉ (NewRequiredParam ℓ k p lkOld lkNew req) =
  NewRequiredParam ℓ k p lkOld
    (lookupParam-there
      (λ eq → ∉-elim h∉ (subst (_∈ paramKeys _) (sym eq) (lookupParam→∈ lkNew)))
      lkNew)
    req

liftNewRequiredFailure {h = h} h∉ (NewRequiredOptionalInOld ℓ k pOld p lkOld lkNew pOldReq req) =
  NewRequiredOptionalInOld ℓ k pOld p lkOld
    (lookupParam-there
      (λ eq → ∉-elim h∉ (subst (_∈ paramKeys _) (sym eq) (lookupParam→∈ lkNew)))
      lkNew)
    pOldReq
    req
```

```agda
-- Walk new params, verify required ones existed in old (or were optional there)
NewRequiredSafe? : (old new : List Parameter) → Unique (paramKeys new) → Dec (NewRequiredSafe old new)
NewRequiredSafe? old [] _ = yes (λ ())
NewRequiredSafe? old (h :: rest)
  (uniq::_ h∉rest uniqRest)
  with Parameter.required h in hReq
  | lookupParam (Parameter.location h) (Parameter.name h) old in lkOldH
  | NewRequiredSafe? old rest uniqRest
  
... | false | _ | yes tail = yes (λ {ℓ} {k} {p} lk req →
    tail {ℓ} {k} {p} (strip lk req) req)
  where
    strip : ∀ {ℓ k p}
          → lookupParam ℓ k (h :: rest) ≡ just p
          → Parameter.required p ≡ true
          → lookupParam ℓ k rest ≡ just p
    strip {ℓ} {k} {p} lk req
      with ParamLocation≟ ℓ (Parameter.location h)
    ... | no  _    = lk
    ... | yes refl
      with k ≟ Parameter.name h
    ... | no  _    = lk
    ... | yes refl =
            ⊥-elim (false≢true (trans (sym hReq)
                                  (subst (λ x → Parameter.required x ≡ true)
                                    (sym (just-inj lk)) req)))

... | false | _ | no ¬tail =
    no λ safe → ¬tail λ {ℓ} {k} {p} lk req →
      safe (lookupParam-there
              (λ eq → ∉-elim h∉rest (subst (_∈ paramKeys _) (sym eq) (lookupParam→∈ lk)))
              lk)
           req

... | true | nothing | _ =
    no λ safe →
      let (pOld , (lkOld , _)) = safe {Parameter.location h} {Parameter.name h} {h} lookupParam-here hReq
      in just≢nothing (trans (sym lkOld) lkOldH)

... | true | just pOld | tailDec
    with Parameter.required pOld in pOldReq
    | tailDec

... | false | _ =
      no λ safe →
        let (pOld' , (lkOld' , reqOld')) = safe {Parameter.location h} {Parameter.name h} {h} lookupParam-here hReq
            pOld≡pOld' = just-inj (trans (sym lkOld') lkOldH)
        in false≢true (trans (sym pOldReq) (trans (cong Parameter.required (sym pOld≡pOld')) reqOld'))

... | true | no ¬tail =
      no λ safe → ¬tail λ {ℓ} {k} {p} lk req →
        safe (lookupParam-there
                (λ eq → ∉-elim h∉rest (subst (_∈ paramKeys _) (sym eq) (lookupParam→∈ lk)))
                lk)
             req

... | true | yes tail = yes dispatch
  where
    dispatch : NewRequiredSafe old (h :: rest)
    dispatch {ℓ} {k} {p} lk req
      with ParamLocation≟ ℓ (Parameter.location h)
    ... | no  _    = tail lk req
    ... | yes refl with k ≟ Parameter.name h
    ... | no  _    = tail lk req
    ... | yes refl = pOld , (lkOldH , pOldReq)
```

```agda
extractFailure :
  ∀ old new
  → Unique (paramKeys new)
  → (NewRequiredSafe old new → ⊥)
  → NewRequiredFailure old new

extractFailure old [] uniq ¬safe =
  ⊥-elim (¬safe (λ ()))

extractFailure old (h :: rest) (uniq::_ h∉rest uniqRest) ¬safe

  with Parameter.required h in hReq
    | lookupParam (Parameter.location h) (Parameter.name h) old in lkOldH
... | false | _ =
      liftNewRequiredFailure h∉rest
        (extractFailure old rest uniqRest
          (λ safe →
             ¬safe
               (λ {ℓ} {k} {p} lk req →
                  safe
                    (lookupParam-strip {ℓ} hReq lk req)
                    req)))
... | true | nothing =
      NewRequiredParam
        (Parameter.location h) (Parameter.name h) h
        lkOldH lookupParam-here hReq
... | true | just pOld

  with Parameter.required pOld in pOldReq
... | true =
      liftNewRequiredFailure h∉rest
        (extractFailure old rest uniqRest
          (λ safe → ¬safe (dispatch safe)))
  where
    dispatch : NewRequiredSafe old rest → NewRequiredSafe old (h :: rest)
    dispatch safe {ℓ} {k} {p} lk req
      with ParamLocation≟ ℓ (Parameter.location h)
    ... | no  _    = safe lk req
    ... | yes refl
      with k ≟ Parameter.name h
    ... | no  _    = safe lk req
    ... | yes refl = pOld , (lkOldH , pOldReq)
... | false =
      NewRequiredOptionalInOld
        (Parameter.location h) (Parameter.name h) pOld h
        lkOldH lookupParam-here pOldReq hReq
```

```agda
-- Convert Dec to sum type
NewRequiredSafe∔ :
  (old new : List Parameter)
  → Unique (paramKeys new)
  → NewRequiredSafe old new ∔ NewRequiredFailure old new

NewRequiredSafe∔ old new uniq
  with NewRequiredSafe? old new uniq
... | yes safe = inl safe
... | no ¬safe = inr (extractFailure old new uniq ¬safe)
```

### 2.1.3 Combining the Checks

```agda
-- Run both sub-checks, pair their witnesses or return the first failure
Params⊑Contra? :
  (old new : List Parameter)
  → Unique (paramKeys old)
  → Unique (paramKeys new)
  → Params⊑Contra old new ∔ (ParamFailure old new ∔ NewRequiredFailure old new)
Params⊑Contra? old new uniqOld uniqNew
  with OldParamsPreserved? old new uniqOld
  | NewRequiredSafe∔ old new uniqNew
... | inr pf   | _        = inr (inl pf)
... | inl _    | inr nrf  = inr (inr nrf)
... | inl old' | inl new' = inl (old' , new')
```

### 2.2 Body Refinement

Request bodies are contravariant in their schema. The check is straightforward: match constructors, recurse on schemas, or succeed trivially for `NoBody` cases.

```agda
data BodyDrift : ∀ {m} → Body m → Body m → Set where

  BodySchemaDrift :
      ∀ {s₀ s₁}
      → SchemaDrift s₁ s₀
      → BodyDrift (HasBody s₀) (HasBody s₁)

  BodySchemaUDrift :
      ∀ {s₀ s₁}
      → SchemaDrift s₁ s₀
      → BodyDrift (HasBodyU s₀) (HasBodyU s₁)

  BodySchemaPDrift :
      ∀ {s₀ s₁}
      → SchemaDrift s₁ s₀
      → BodyDrift (HasBodyP s₀) (HasBodyP s₁)
```

```agda
Body⊑Contra? : ∀ {m} → (b₀ b₁ : Body m) → WFBody b₀ → WFBody b₁ → Body⊑Contra (refl) b₀ b₁ ∔ BodyDrift b₀ b₁

Body⊑Contra? NoBody  NoBody  _ _ = inl tt

Body⊑Contra? NoBodyD NoBodyD _ _ = inl tt

Body⊑Contra? (HasBody s) (HasBody t) (wf-hasBody ws) (wf-hasBody wt)
  with Schema⊑Co? wt ws
... | inl ok    = inl ok
... | inr drift = inr (BodySchemaDrift drift)

Body⊑Contra? (HasBodyU s) (HasBodyU t) (wf-hasBodyU ws) (wf-hasBodyU wt)
  with Schema⊑Co? wt ws
... | inl ok    =  inl ok
... | inr drift = inr (BodySchemaUDrift drift)

Body⊑Contra? (HasBodyP s) (HasBodyP t) (wf-hasBodyP ws) (wf-hasBodyP wt)
  with Schema⊑Co? wt ws
... | inl ok    = inl ok
... | inr drift = inr (BodySchemaPDrift drift)
```

### 2.3 Response Refinement

Responses are covariant: every response in the old spec must be preserved in the new spec with a covariant schema change. We walk the old list, look up each status code in the new list, and check schema refinement recursively.

```agda
data RespFailure (old new : List Response) : Set where
  RespRemoved :
      (st : Status)
    → lookupResp st old ≢ nothing
    → lookupResp st new ≡ nothing
    → RespFailure old new

  RespDrift :
      (st : Status) (s t : Schema)
    → lookupResp st old ≡ just s
    → lookupResp st new ≡ just t
    → SchemaDrift s t
    → RespFailure old new
```

```agda
-- Lift a tail failure to the full list
liftRespFailure :
    ∀ {st₀ s₀ rs new}
  → st₀ ∉ respKeys rs
  → RespFailure rs new
  → RespFailure (response st₀ s₀ :: rs) new

liftRespFailure {st₀} {s₀} {rs} st₀∉ (RespRemoved st notNoth missing) =
  RespRemoved st notNoth' missing
  where
    notNoth' : lookupResp st (response st₀ s₀ :: rs) ≢ nothing
    notNoth' contra
      with Status≟ st st₀
    ... | yes refl = just≢nothing contra
    ... | no  _    = notNoth contra

liftRespFailure {st₀} {rs = rs} st₀∉ (RespDrift st s t lkOld lkNew d) =
  RespDrift st s t
    (lookupResp-there
      (λ eq → ∉-elim st₀∉ (subst (_∈ respKeys rs) (sym eq) (lookupResp→∈ lkOld)))
      lkOld)
    lkNew
    d
```

```agda
Resps⊑Co? :
    (old new : List Response)
  → Unique (respKeys old)
  → All WFResponse old
  → All WFResponse new
  → Resps⊑Co old new ∔ RespFailure old new
  
Resps⊑Co? [] new _ _ _ = inl tt

Resps⊑Co? (response st s :: rs) new
  (uniq::_ st∉ uniqRest)
  (all::_ (wf-response wfS) wfRs)
  wfNew
  with lookupResp st new in lkeq
... | nothing =
      inr (RespRemoved st
            (λ contra → just≢nothing (trans (sym (lookupResp-here {st})) contra))
            lkeq)
... | just t
  with Schema⊑Co? wfS (lookupResp-wf wfNew lkeq)
  | Resps⊑Co? rs new uniqRest wfRs wfNew
... | inr d    | _         = inr (RespDrift st s t (lookupResp-here {st}) lkeq d)
... | inl _    | inr tailF = inr (liftRespFailure st∉ tailF)
... | inl ok   | inl tail  = inl ((t , (refl , ok)) , tail)
```

### 2.4 Endpoint Refinement

With all component checks in place, we run them in sequence: check route/method identity first, then parameters, body, and responses. Any failure gets converted to the appropriate `EndpointDrift` constructor.

```agda
-- Extract well-formedness facts from WFEndpoint
wfEndpoint-paramUniq : ∀ {e} → WFEndpoint e → Unique (paramKeys (Endpoint.parameters e))
wfEndpoint-paramUniq (wf-endpoint _ _ uniq _ _ _) = uniq

wfEndpoint-respUniq : ∀ {e} → WFEndpoint e → Unique (respKeys (Endpoint.responses e))
wfEndpoint-respUniq (wf-endpoint _ _ _ _ _ uniq) = uniq

wfEndpoint-body : ∀ {e} → WFEndpoint e → WFBody (Endpoint.body e)
wfEndpoint-body (wf-endpoint _ _ _ body _ _) = body

wfEndpoint-resps : ∀ {e} → WFEndpoint e → All WFResponse (Endpoint.responses e)
wfEndpoint-resps (wf-endpoint _ _ _ _ resps _) = resps
```

```agda
-- Convert local failures to EndpointDrift
paramFailure→EndpointDrift :
    ∀ {e₀ e₁}
    → ParamFailure (Endpoint.parameters e₀) (Endpoint.parameters e₁)
  → EndpointDrift e₀ e₁
paramFailure→EndpointDrift (ParamRemoved ℓ k notNoth missing) =
  ParameterRemoved notNoth missing
paramFailure→EndpointDrift (ParamSchemaChanged p₀ p₁ loc≡ name≡ lk₀ lk₁ sch≢) =
  ParameterSchemaChanged loc≡ name≡ lk₀ lk₁ sch≢
paramFailure→EndpointDrift (RequiredParamAdded p₀ p₁ loc≡ name≡ lk₀ lk₁ req₀ req₁) =
  RequiredParameterAdded loc≡ name≡ lk₀ lk₁ req₀ req₁
```

```agda
newRequiredFailure→EndpointDrift :
    ∀ {e₀ e₁}
  → NewRequiredFailure (Endpoint.parameters e₀) (Endpoint.parameters e₁)
  → EndpointDrift e₀ e₁
newRequiredFailure→EndpointDrift (NewRequiredParam ℓ k p lkOld lkNew req) =
  NewRequiredParameter lkOld lkNew req
newRequiredFailure→EndpointDrift {e₀} {e₁} (NewRequiredOptionalInOld ℓ k pOld p lkOld lkNew pOldReq req) =
  RequiredParameterAdded
    {p₀ = pOld} {p₁ = p}
    (trans (lookupParam-location {ps = Endpoint.parameters e₀} lkOld)
           (sym (lookupParam-location {ps = Endpoint.parameters e₁} lkNew)))
    (trans (lookupParam-name {ps = Endpoint.parameters e₀} lkOld)
           (sym (lookupParam-name {ps = Endpoint.parameters e₁} lkNew)))
    (lookupParam-self {ps = Endpoint.parameters e₀} lkOld)
    (lookupParam-self {ps = Endpoint.parameters e₁} lkNew)
    pOldReq
    req
```

```agda
bodyDrift→EndpointDrift :
    ∀ {e₀ e₁}
  → (method≡ : Endpoint.method e₀ ≡ Endpoint.method e₁)
  → BodyDrift (Endpoint.body e₀) (subst Body (sym method≡) (Endpoint.body e₁))
  → EndpointDrift e₀ e₁
bodyDrift→EndpointDrift refl (BodySchemaDrift  d) = BodySchemaDrift body-post  body-post  d
bodyDrift→EndpointDrift refl (BodySchemaUDrift d) = BodySchemaDrift body-put   body-put   d
bodyDrift→EndpointDrift refl (BodySchemaPDrift d) = BodySchemaDrift body-patch body-patch d
```

```agda
respFailure→EndpointDrift :
    ∀ {e₀ e₁}
  → RespFailure (Endpoint.responses e₀) (Endpoint.responses e₁)
  → EndpointDrift e₀ e₁
respFailure→EndpointDrift (RespRemoved st notNoth missing) =
  ResponseRemoved notNoth missing
respFailure→EndpointDrift (RespDrift st s t lkOld lkNew d) =
  ResponseDrift lkOld lkNew d
```

```agda
Endpoint⊑? : (e₀ e₁ : Endpoint) → WFEndpoint e₀ → WFEndpoint e₁ → Endpoint⊑ e₀ e₁ ∔ EndpointDrift e₀ e₁
Endpoint⊑? e₀ e₁ wf₀ wf₁
  with Path≟ (Endpoint.route e₀) (Endpoint.route e₁)
... | no  route≢ = inr (RouteChanged route≢)
... | yes route≡

  with Method≟ (Endpoint.method e₀) (Endpoint.method e₁)
... | no  method≢ = inr (MethodChanged method≢)
... | yes refl

  with Params⊑Contra? (Endpoint.parameters e₀) (Endpoint.parameters e₁) (wfEndpoint-paramUniq wf₀) (wfEndpoint-paramUniq wf₁)
... | inr (inl pf)  = inr (paramFailure→EndpointDrift pf)
... | inr (inr nrf) = inr (newRequiredFailure→EndpointDrift nrf)
... | inl params

  with Body⊑Contra? (Endpoint.body e₀) (Endpoint.body e₁) (wfEndpoint-body wf₀) (wfEndpoint-body wf₁)
... | inr bodyD = inr (bodyDrift→EndpointDrift refl bodyD)
... | inl body

  with Resps⊑Co? (Endpoint.responses e₀) (Endpoint.responses e₁) (wfEndpoint-respUniq wf₀) (wfEndpoint-resps wf₀) (wfEndpoint-resps wf₁)
... | inr respF = inr (respFailure→EndpointDrift respF)
... | inl resps = inl (⊑-endpoint wf₀ wf₁ route≡ refl params body resps)
```

---

## 3. API Refinement

We now lift refinement decidability to whole APIs. Since endpoint and schema refinement are already decidable, this reduces to aligning components and endpoints via lookup and running recursive checks on matched entries. Failures get packaged into `Drift` witnesses that point to exactly what was removed or what changed.

### 3.1 Components

```agda
data ComponentFailure (old new : List (String × Schema)) : Set where

  ComponentRemoved' :
      (k : String)
    → lookupComponent k old ≢ nothing
    → lookupComponent k new ≡ nothing
    → ComponentFailure old new
    
  ComponentDrift' :
      (k : String) (s t : Schema)
    → lookupComponent k old ≡ just s
    → lookupComponent k new ≡ just t
    → SchemaDrift s t
    → ComponentFailure old new
```

```agda
-- Lift a tail failure to the full list
liftComponentFailure :
    ∀ {k₀ s₀ cs new}
  → k₀ ∉ keys cs
  → ComponentFailure cs new
  → ComponentFailure ((k₀ , s₀) :: cs) new
  
liftComponentFailure {k₀} {s₀} {cs} k₀∉ (ComponentRemoved' k notNoth missing) =
  ComponentRemoved' k
    (λ contra → notNoth (strip contra))
    missing
  where
    strip : lookupComponent k ((k₀ , s₀) :: cs) ≡ nothing
          → lookupComponent k cs ≡ nothing
    strip contra with k ≟ k₀
    ... | yes refl = ⊥-elim (just≢nothing contra)
    ... | no  _    = contra
    
liftComponentFailure k₀∉ (ComponentDrift' k s t lkOld lkNew d) =
  ComponentDrift' k s t
    (lookupComponent-there
      (λ eq → ∉-elim k₀∉ (subst (_∈ keys _) (sym eq) (lookupComponent→∈ lkOld)))
      lkOld)
    lkNew
    d
```

```agda
-- Extract well-formedness from a component lookup
lookupComponent-wf :
  ∀ {k s cs}
  → All WFSchema (values cs)
  → lookupComponent k cs ≡ just s
  → WFSchema s
  
lookupComponent-wf {k} {cs = []} _ ()

lookupComponent-wf {k} {cs = (k' , s') :: cs} (all::_ wfS rest) lk
  with k ≟ k'
... | yes refl = subst WFSchema (just-inj lk) wfS
... | no  _    = lookupComponent-wf rest lk
```

```agda
Components⊑? :
    (old new : List (String × Schema))
  → Unique (keys old)
  → All WFSchema (values old)
  → All WFSchema (values new)
  → Components⊑ old new ∔ ComponentFailure old new
  
Components⊑? [] new _ _ _ = inl tt

Components⊑? ((k , s) :: cs) new (uniq::_ k∉ uniqRest) (all::_ wfS wfRest) wfNew
  with lookupComponent k new in lkeq
... | nothing =
      inr (ComponentRemoved' k
            (λ contra → just≢nothing (trans (sym (lookupComponent-here {k})) contra))
            lkeq)
... | just t
  with Schema⊑Co? wfS (lookupComponent-wf wfNew lkeq)
  | Components⊑? cs new uniqRest wfRest wfNew
... | inr d  | _        = inr (ComponentDrift' k s t (lookupComponent-here {k}) lkeq d)
... | inl _  | inr fail = inr (liftComponentFailure k∉ fail)
... | inl ok | inl rest = inl ((t , (refl , ok)) , rest)
```

### 3.2 Endpoints

```agda
data EndpointFailure (old new : List Endpoint) : Set where

  EndpointRemoved' :
      (r : Path) (m : Method)
    → lookupEndpoint r m old ≢ nothing
    → lookupEndpoint r m new ≡ nothing
    → EndpointFailure old new
    
  EndpointDrift' :
      (r : Path) (m : Method) (e₀ e₁ : Endpoint)
    → lookupEndpoint r m old ≡ just e₀
    → lookupEndpoint r m new ≡ just e₁
    → EndpointDrift e₀ e₁
    → EndpointFailure old new
```

```agda
-- Extract well-formedness from an endpoint lookup
lookupEndpoint-wf :
  ∀ {r m e es}
  → All WFEndpoint es
  → lookupEndpoint r m es ≡ just e
  → WFEndpoint e
lookupEndpoint-wf {r} {m} {es = e :: es} (all::_ wfE wfRest) lk
  with Path≟ r (Endpoint.route e)
... | no  _    = lookupEndpoint-wf wfRest lk
... | yes refl
  with Method≟ m (Endpoint.method e)
... | no  _    = lookupEndpoint-wf wfRest lk
... | yes refl = subst WFEndpoint (just-inj lk) wfE
lookupEndpoint-wf {es = []} all[] ()
```

```agda
-- Lift a tail failure to the full list
liftEndpointFailure :
    ∀ {h es new}
  → (Endpoint.route h , Endpoint.method h) ∉ endpointKeys es
  → EndpointFailure es new
  → EndpointFailure (h :: es) new
  
liftEndpointFailure {h} {es} {new} h∉ (EndpointRemoved' r m notNoth missing) =
  EndpointRemoved' r m
    (λ contra → notNoth (strip contra))
    missing
  where
    strip : lookupEndpoint r m (h :: es) ≡ nothing
          → lookupEndpoint r m es ≡ nothing
    strip contra
      with Path≟ r (Endpoint.route h)
    ... | no  _    = contra
    ... | yes refl
      with Method≟ m (Endpoint.method h)
    ... | no  _    = contra
    ... | yes refl = ⊥-elim (just≢nothing contra)
    
liftEndpointFailure h∉ (EndpointDrift' r m e₀ e₁ lkOld lkNew d) =
  EndpointDrift' r m e₀ e₁
    (lookupEndpoint-there
      (λ eq → ∉-elim h∉ (subst (_∈ endpointKeys _) (sym eq) (lookupEndpoint→∈ lkOld)))
      lkOld)
    lkNew
    d
```

```agda
Endpoints⊑? :
    (old new : List Endpoint)
  → Unique (endpointKeys old)
  → All WFEndpoint old
  → All WFEndpoint new
  → Endpoints⊑ old new ∔ EndpointFailure old new
Endpoints⊑? [] new _ _ _ = inl tt
Endpoints⊑? (e :: es) new (uniq::_ e∉ uniqRest) (all::_ wfE wfRest) wfNew
  with lookupEndpoint (Endpoint.route e) (Endpoint.method e) new in lkeq
... | nothing =
      inr (EndpointRemoved'
            (Endpoint.route e) (Endpoint.method e)
            (λ contra → just≢nothing (trans (sym (lookupEndpoint-here {e})) contra))
            lkeq)
... | just e'
  with Endpoint⊑? e e' wfE (lookupEndpoint-wf wfNew lkeq)
  | Endpoints⊑? es new uniqRest wfRest wfNew
... | inr d  | _        = inr (EndpointDrift' _ _ e e' lookupEndpoint-here lkeq d)
... | inl _  | inr fail = inr (liftEndpointFailure e∉ fail)
... | inl ok | inl rest = inl ((e' , (refl , ok)) , rest)
```

### 3.3 Putting it together

```agda
-- Extract well-formedness facts from WFAPI
wfAPI-components : ∀ {a} → WFAPI a → All WFSchema (values (API.components a))
wfAPI-components (wf-api wfComps _ _ _) = wfComps

wfAPI-componentUniq : ∀ {a} → WFAPI a → Unique (keys (API.components a))
wfAPI-componentUniq (wf-api _ uniq _ _) = uniq

wfAPI-paths : ∀ {a} → WFAPI a → All WFEndpoint (API.paths a)
wfAPI-paths (wf-api _ _ wfPaths _) = wfPaths

wfAPI-pathUniq : ∀ {a} → WFAPI a → Unique (endpointKeys (API.paths a))
wfAPI-pathUniq (wf-api _ _ _ uniq) = uniq
```

```agda
-- Convert local failures to API-level Drift
componentFailure→Drift : ∀ {a₀ a₁} → ComponentFailure (API.components a₀) (API.components a₁) → Drift a₀ a₁
componentFailure→Drift (ComponentRemoved' k notNoth missing) = ComponentRemoved notNoth missing
componentFailure→Drift (ComponentDrift' k s t lkOld lkNew d) = ComponentDriftWitness lkOld lkNew d
```

```agda
endpointFailure→Drift : ∀ {a₀ a₁} → EndpointFailure (API.paths a₀) (API.paths a₁) → Drift a₀ a₁
endpointFailure→Drift (EndpointRemoved' r m notNoth missing) = EndpointRemoved notNoth missing
endpointFailure→Drift (EndpointDrift' r m e₀ e₁ lkOld lkNew d) = EndpointDriftWitness lkOld lkNew d
```

```agda
API⊑? : (a₀ a₁ : API) → WFAPI a₀ → WFAPI a₁ → API⊑ a₀ a₁ ∔ Drift a₀ a₁
API⊑? a₀ a₁ wf₀ wf₁
  with Components⊑?
         (API.components a₀) (API.components a₁)
         (wfAPI-componentUniq wf₀)
         (wfAPI-components wf₀)
         (wfAPI-components wf₁)
... | inr fail = inr (componentFailure→Drift fail)
... | inl comps
  with Endpoints⊑?
         (API.paths a₀) (API.paths a₁)
         (wfAPI-pathUniq wf₀)
         (wfAPI-paths wf₀)
         (wfAPI-paths wf₁)
... | inr fail = inr (endpointFailure→Drift fail)
... | inl eps  = inl (⊑-api wf₀ wf₁ comps eps)
```

---

## 4. Main Result

We now have a complete decision procedure for API refinement. Given two well-formed APIs, `API⊑?` either constructs a refinement proof or returns a concrete drift witness explaining the incompatibility.

The result type `API⊑ a₀ a₁ ∔ Drift a₀ a₁` gives us both positive evidence (a refinement proof when compatible) and negative evidence (a structural witness explaining exactly what broke when incompatible).

This is the algorithmic core of compatibility checking. In `Semantics.DriftProperties`, we combine this with soundness of drift (`Drift → ¬Refinement`) to obtain the standard `Dec (API⊑ a₀ a₁)` result.
