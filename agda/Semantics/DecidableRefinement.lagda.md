# Decidable Refinement

Refinement and drift describe the same situation from opposite directions. Given two well-formed specifications, we can either build a proof that one safely refines the other, or point to a specific structural change that breaks compatibility.

The construction works bottom-up. We start at the schema level, deciding refinement by structural recursion on shape and returning either a `Schema⊑Co` proof or a `SchemaDrift` witness. We then lift this to endpoints by checking parameters, request bodies, and responses. Finally, we lift again to APIs by aligning components and endpoints via lookup.

All checks are constructive and run over finite structures. They depend only on decidable equality for identifiers and recursive calls on smaller pieces of the specification. Well-formedness plays a crucial role: it guarantees uniqueness of keys and ensures that every alignment step is deterministic and computable.

```agda
module Semantics.DecidableRefinement where

open import Prelude
open import Syntax.Syntax
open import Syntax.Decidable

open import WellFormed.Core
open import WellFormed.Lemmas

open import Semantics.Variance

open import Semantics.SchemaRefinement
open import Semantics.SchemaRefinementProperties
  using (lookupProp-here; lookupProp-skip; lookupProp-∉-nothing; ⊑Co-refl; ⊑Co-trans; prim≢array; prim≢object)

open import Semantics.EndpointRefinement
open import Semantics.APIRefinement

open import Semantics.Drift

open Σ using (fst ; snd)
```

## 1. Decidability of Covariant Schema Refinement

We decide covariant schema refinement by structural recursion on schema shape. The procedure follows the constructors of `Schema⊑Co`. When refinement succeeds we return `inl` with a proof; when it fails we return `inr` with a `SchemaDrift` witness explaining the structural violation.

### 1.1 Decidable Property Refinement

The object case reduces to property alignment. For each property in the old schema, we check that it exists in the new schema and that its schema refines recursively. Failure is recorded as a `PropertyFailure`, which is later converted into a `SchemaDrift`.

`PropsRefine?` and `Schema⊑Co?` are mutually recursive because object refinement requires recursive schema checks on property types.

### Helpers

```agda
data PropertyFailure
  (ps qs : List (String × Schema)) : Set where

  MissingProperty :
      (k : String)
    → lookupProp k ps ≢ nothing
    → lookupProp k qs ≡ nothing
    → PropertyFailure ps qs

  NestedDrift :
      (k : String)
      (si ti : Schema)
    → lookupProp k ps ≡ just si
    → lookupProp k qs ≡ just ti
    → SchemaDrift si ti
    → PropertyFailure ps qs
```

```agda
lookupProp-wf : ∀ {k s ps} → All WFSchema (values ps) → lookupProp k ps ≡ just s → WFSchema s
lookupProp-wf {k} {s} {[]} _ ()
lookupProp-wf {k} {s} {(k' , s') :: ps} (all::_ wfS wfRest) lk
  with k ≟ k'
... | yes refl = subst WFSchema (just-inj lk) wfS
... | no  _    = lookupProp-wf wfRest lk
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

### Decision Procedure

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
        inr (MissingProperty k (λ contra → just≢nothing (trans (sym lookupProp-here) contra)) eq)

  -- Property exists
  ... | just t
    with Schema⊑Co? wfS (lookupProp-wf wfQs eq)
    
  -- Nested schema drift
  ... | inr d =
        inr (NestedDrift k s t lookupProp-here eq d)

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

---

### 1.2 Decidable Covariant Schema Refinement

```agda
  Schema⊑Co? :
    ∀ {s t}
    → WFSchema s
    → WFSchema t
    → Schema⊑Co s t ∔ SchemaDrift s t
```

### Primitives

```agda
  Schema⊑Co? {s} {t}
    wfS@(wf-prim primS _ _ _)
    wfT@(wf-prim primT _ _ _)
    with Base≟ (Schema.type s) (Schema.type t)
  ... | yes refl =
        inl (⊑-prim wfS wfT primS primT refl)

  ... | no neq =
        inr (PrimitiveChanged primS primT neq)
```

### Arrays

```agda
  Schema⊑Co? {s} {t}
    wfS@(wf-array tyS itemsS wfItemS _ _)
    wfT@(wf-array tyT itemsT wfItemT _ _)
    with Schema⊑Co? wfItemS wfItemT
  ... | inl r =
        inl (⊑-array wfS wfT tyS tyT itemsS itemsT r)

  ... | inr d =
        inr (ArrayItemDrift tyS tyT itemsS itemsT d)
```

### Objects

```agda
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
```

### Shape mismatches

```agda
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

The procedure is total and structurally recursive on the schema shape. Each negative branch corresponds directly to one of the constructors of `SchemaDrift`, ensuring that failure always carries a structured explanation.

---

## 2. Decidability of Endpoint Refinement

Endpoint refinement decomposes into four independent checks:

1. parameter contravariance,
2. request body contravariance,
3. response covariance, and
4. route/method identity.

Each check is decided separately and failures are packaged into the corresponding `EndpointDrift` constructor.


### 2.1 Decidable Parameter Refinement

Parameter contravariance splits into two checks: `OldParamsPreserved?` scans the old list ensuring every parameter is preserved compatibly, and `NewRequiredSafe?` scans the new list ensuring no new required parameter is introduced. Failures are recorded separately and converted to `EndpointDrift`.

---

### `OldParamsPreserved`

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

### Decision

```agda
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

-- required stays false
... | false | false
  with OldParamsPreserved? ps new uniqTail
... | inl rest = inl ((q , (refl , (sym (lookupParam-location {Parameter.location p} {Parameter.name p} {new} {q} lkeq) , (sym (lookupParam-name {Parameter.location p} {Parameter.name p} {new} {q} lkeq) , (refl , (λ req≡true → ⊥-elim (false≢true (trans (sym reqQ) req≡true)))))))) , rest)

... | inr pf   = inr (liftParamFailure p∉tail pf)

OldParamsPreserved? (p :: ps) new (uniq::_ p∉tail uniqTail)
  | just q | yes refl | true | false
  with OldParamsPreserved? ps new uniqTail
... | inl rest = inl ((q , (refl , (sym (lookupParam-location {Parameter.location p} {Parameter.name p} {new} {q} lkeq) , (sym (lookupParam-name {Parameter.location p} {Parameter.name p} {new} {q} lkeq) , (refl , (λ req≡true → ⊥-elim (false≢true (trans (sym reqQ) req≡true)))))))) , rest)

... | inr pf   = inr (liftParamFailure p∉tail pf)

OldParamsPreserved? (p :: ps) new (uniq::_ p∉tail uniqTail)
  | just q | yes refl | true | true
  with OldParamsPreserved? ps new uniqTail
... | inl rest = inl ((q , (refl , (sym (lookupParam-location {Parameter.location p} {Parameter.name p} {new} {q} lkeq) , (sym (lookupParam-name {Parameter.location p} {Parameter.name p} {new} {q}  lkeq) , (refl , (λ _ → refl)))))) , rest)
... | inr pf   = inr (liftParamFailure p∉tail pf)
```

---

### `NewRequiredSafe`

### Helpers

```agda
data NewRequiredFailure (old new : List Parameter) : Set where
  NewRequiredParam :
      (ℓ : ParamLocation) (k : String) (p : Parameter)
    → lookupParam ℓ k old ≡ nothing
    → lookupParam ℓ k new ≡ just p
    → Parameter.required p ≡ true
    → NewRequiredFailure old new

```

```agda
liftNewRequiredFailure :
  ∀ {old rest h}
  → NewRequiredFailure old rest
  → NewRequiredFailure old (h :: rest)

liftNewRequiredFailure (NewRequiredParam ℓ k p lkOld lkNew req) =
  NewRequiredParam ℓ k p lkOld (lookupParam-there {!!} lkNew) req
```

### Decision

```agda
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

NewRequiredSafe? :
  (old new : List Parameter)
  → Unique (paramKeys new)
  → NewRequiredSafe old new ∔ NewRequiredFailure old new

NewRequiredSafe? old [] _ =
  inl (λ ())

NewRequiredSafe? old (h :: rest)
  (uniq::_ h∉rest uniqRest)
  with Parameter.required h in hReq
     | lookupParam (Parameter.location h) (Parameter.name h) old in lkOldH
     | NewRequiredSafe? old rest uniqRest

-- optional parameter, tail safe
... | false | _ | inl tail =
  inl (λ {ℓ} {k} {p} lk req → tail (lookupParam-strip {ℓ} {k} {p} hReq lk req) req)

-- optional parameter, tail fails
... | false | _ | inr tailFail =
  inr (liftNewRequiredFailure tailFail)

-- required parameter missing in old
... | true | nothing | _ =
  inr (NewRequiredParam (Parameter.location h) (Parameter.name h) h lkOldH lookupParam-here hReq)

-- required parameter exists in old
... | true | just pOld | tailRes
  with Parameter.required pOld in pOldReq
     | tailRes

-- old parameter not required → failure
... | false | inl tail =
  inl (λ {ℓ} {k} {p} lk req →
        tail (lookupParam-strip {ℓ} {k} {p} hReq lk req) req)


... | false | inr tailFail =
  inr (liftNewRequiredFailure tailFail)

-- tail fails
... | true | inr tailFail =
  inr (liftNewRequiredFailure tailFail)

-- everything safe
... | true | inl tail =
  inl dispatch
  where
    dispatch : NewRequiredSafe old (h :: rest)
    dispatch {ℓ} {k} {p} lk req
      with ParamLocation≟ ℓ (Parameter.location h)
    ... | no _ = tail lk req

    ... | yes refl
      with k ≟ Parameter.name h
    ... | no _ = tail lk req

    ... | yes refl =
      pOld , (lkOldH , pOldReq)


```agda

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
    no λ safe → ¬tail λ {ℓ} {k} {p} lk req → safe (lift lk) req
  where
    lift : ∀ {ℓ k p}
         → lookupParam ℓ k rest ≡ just p
         → lookupParam ℓ k (h :: rest) ≡ just p
    lift {ℓ} {k} lk
      with ParamLocation≟ ℓ (Parameter.location h)
    ... | no  _    = lk
    ... | yes refl with k ≟ Parameter.name h
    ... | no  _    = lk
    ... | yes refl = ⊥-elim (∉-elim h∉rest (lookupParam→∈ lk))

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
      no λ safe → ¬tail λ {ℓ} {k} {p} lk req → safe (lift lk) req
  where
    lift : ∀ {ℓ k p}
         → lookupParam ℓ k rest ≡ just p
         → lookupParam ℓ k (h :: rest) ≡ just p
    lift {ℓ} {k} lk
      with ParamLocation≟ ℓ (Parameter.location h)
    ... | no  _    = lk
    ... | yes refl with k ≟ Parameter.name h
    ... | no  _    = lk
    ... | yes refl = ⊥-elim (∉-elim h∉rest (lookupParam→∈ lk))

... | true | yes tail = yes dispatch
  where
    dispatch : NewRequiredSafe old (h :: rest)
    dispatch {ℓ} {k} {p} lk req
      with ParamLocation≟ ℓ (Parameter.location h)
    ... | no  _    = tail lk req
    ... | yes refl with k ≟ Parameter.name h
    ... | no  _    = tail lk req
    ... | yes refl = pOld , (lkOldH , pOldReq)

extractFailure :
  ∀ old new
  → Unique (paramKeys new)
  → (NewRequiredSafe old new → ⊥)
  → NewRequiredFailure old new

extractFailure old [] uniq ¬safe =
  ⊥-elim (¬safe (λ ()))

extractFailure old (h :: rest) (uniq::_ h∉rest uniqRest) ¬safe
  with Parameter.required h
     | lookupParam (Parameter.location h) (Parameter.name h) old

-- optional parameter → cannot violate the rule
... | false | _ =
      liftNewRequiredFailure
        (extractFailure old rest uniqRest
          (λ safe →
             ¬safe
               (λ {ℓ} {k} {p} lk req →
                  safe
                    {!!}
                    req)))
                    
-- required parameter missing in old → real failure
... | true | nothing =
      NewRequiredParam
        (Parameter.location h)
        (Parameter.name h)
        h
        {!!}
        lookupParam-here
        {!!}

-- required parameter exists in old
... | true | just pOld
  with Parameter.required pOld

-- already required in old → recurse
... | true = {!!}

-- optional in old → strengthening (handled by OldParamsPreserved)
... | false = {!!}

NewRequiredSafe∔ :
  (old new : List Parameter)
  → Unique (paramKeys new)
  → NewRequiredSafe old new ∔ NewRequiredFailure old new
```

---


still not fniished w above



---

```agda
Params⊑Contra? :
  (old new : List Parameter)
  → Unique (paramKeys new)
  → Params⊑Contra old new ∔ ParamFailure old new
Params⊑Contra? old new uniq = {!!}

```

---

### 2.2 Decidable Body Refinement

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

---

### 2.3 Decidable Response Refinement

### Helpers

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

### Decision

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


---

### 2.4 Decidable Endpoint Refinement

With all component checks in place, endpoint refinement is decided by running each check in sequence and converting any failure into an `EndpointDrift` witness. The helpers below extract well-formedness invariants from `WFEndpoint` and bridge the local failure types to `EndpointDrift`.


### Helpers

```agda
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

### Decision

```agda
Endpoint⊑? : (e₀ e₁ : Endpoint) → WFEndpoint e₀ → WFEndpoint e₁ → Endpoint⊑ e₀ e₁ ∔ EndpointDrift e₀ e₁
Endpoint⊑? e₀ e₁ wf₀ wf₁
  with Path≟ (Endpoint.route e₀) (Endpoint.route e₁)
... | no  route≢ = inr (RouteChanged route≢)
... | yes route≡
  with Method≟ (Endpoint.method e₀) (Endpoint.method e₁)
... | no  method≢ = inr (MethodChanged method≢)
... | yes refl
  with Params⊑Contra? (Endpoint.parameters e₀) (Endpoint.parameters e₁) (wfEndpoint-paramUniq wf₁)
... | inr paramF = inr (paramFailure→EndpointDrift paramF)
... | inl params
  with Body⊑Contra? (Endpoint.body e₀) (Endpoint.body e₁) (wfEndpoint-body wf₀) (wfEndpoint-body wf₁)
... | inr bodyD = inr (bodyDrift→EndpointDrift refl bodyD)
... | inl body
  with Resps⊑Co? (Endpoint.responses e₀) (Endpoint.responses e₁) (wfEndpoint-respUniq wf₀) (wfEndpoint-resps wf₀) (wfEndpoint-resps wf₁)
... | inr respF = inr (respFailure→EndpointDrift respF)
... | inl resps = inl (⊑-endpoint wf₀ wf₁ route≡ refl params body resps)
```

---

## 3. Decidability of API Refinement

We now lift refinement decidability to whole APIs. Since endpoint and schema refinement are already decidable, API refinement reduces to aligning components and endpoints via lookup and running recursive checks on matched entries. Failures are packaged into `APIDrift` witnesses that identify exactly what was removed or what changed inside a matched entry. As before, well-formedness guarantees uniqueness of keys so alignment is unambiguous.

### 3.1 Decidable Componenent Refinement 

### Helpers

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

### Decision

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
            (λ contra → just≢nothing (trans (sym lookupComponent-here) contra))
            lkeq)
... | just t
  with Schema⊑Co? wfS (lookupComponent-wf wfNew lkeq)
  | Components⊑? cs new uniqRest wfRest wfNew
... | inr d  | _        = inr (ComponentDrift' k s t lookupComponent-here lkeq d)
... | inl _  | inr fail = inr (liftComponentFailure k∉ fail)
... | inl ok | inl rest = inl ((t , (refl , ok)) , rest)
```

---

