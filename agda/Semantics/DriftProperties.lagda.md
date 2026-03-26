# Drift Properties

This module connects drift with refinement failure.

We prove two directions:
- soundness: drift witnesses refute refinement, and
- completeness: refinement failure produces a drift witness.

Together, these show that for well-formed APIs, drift is equivalent to refinement failure.
```agda
module Semantics.DriftProperties where

open import Prelude
open import Syntax.Syntax
open import Syntax.Decidable

open import WellFormed.Core

open import Semantics.Variance
open import Semantics.SchemaRefinement
open import Semantics.SchemaRefinementProperties
open import Semantics.EndpointRefinement
open import Semantics.EndpointRefinementProperties
open import Semantics.APIRefinement
open import Semantics.APIRefinementProperties

open import Semantics.Drift
open import Semantics.DecidableRefinement

open Σ using (fst ; snd)
```

---

## 1. Soundness

Drift witnesses refute refinement. 

Each constructor of drift corresponds to a structural obligation required by refinement, so the proof proceeds by case analysis on the drift witness and the corresponding refinement derivation.

### 1.1. Schema Drift Soundness

```agda
SchemaDriftSound : ∀ {s t} → SchemaDrift s t → ¬ Schema⊑Co s t
```

### `⊑-prim` cases

```agda
SchemaDriftSound (PrimitiveChanged _ _ s≢t)
                 (⊑-prim _ _ _ _ s≡t) =
                   s≢t s≡t

SchemaDriftSound (ArrayItemDrift tyS _ _ _ _)
                 (⊑-prim _ _ primS _ _) =
                   prim≢array (subst IsPrimitive (tyS) primS)

SchemaDriftSound (RequiredFieldRemoved tyS _ _ _)
                 (⊑-prim _ _ primS _ _) =
                   prim≢object (subst IsPrimitive (tyS) primS)

SchemaDriftSound (PropertyRemoved tyS _ _ _)
                 (⊑-prim _ _ primS _ _) =
                   prim≢object (subst IsPrimitive (tyS) primS)

SchemaDriftSound (PropertyDrift tyS _ _ _ _)
                 (⊑-prim _ _ primS _ _)
                   = prim≢object (subst IsPrimitive (tyS) primS)

SchemaDriftSound (ShapeMismatch s≢t)
                 (⊑-prim _ _ _ _ eq)
                   = s≢t eq
```

### `⊑-array` cases

```agda
SchemaDriftSound (PrimitiveChanged primS _ _)
                 (⊑-array _ _ tyS _ _ _ _) =
                   prim≢array (subst IsPrimitive tyS primS)

SchemaDriftSound (ArrayItemDrift _ _ is it d)
                 (⊑-array _ _ _ _ is' it' sub) =
                   SchemaDriftSound
                     (subst (SchemaDrift _)
                       (just-inj (trans (sym it) it'))
                       (subst (λ x → SchemaDrift x _) (just-inj (trans (sym is) is')) d))
                     sub

SchemaDriftSound (RequiredFieldRemoved tyS _ _ _)
                 (⊑-array _ _ tyS' _ _ _ _) =
                   array≢object (trans (sym tyS') tyS)

SchemaDriftSound (PropertyRemoved tyS _ _ _)
                 (⊑-array _ _ tyS' _ _ _ _) =
                   array≢object (trans (sym tyS') tyS)

SchemaDriftSound (PropertyDrift tyS _ _ _ _)
                 (⊑-array _ _ tyS' _ _ _ _) =
                   array≢object (trans (sym tyS') tyS)

SchemaDriftSound (ShapeMismatch s≢t)
                 (⊑-array _ _ tyS tyT _ _ _)
                   = s≢t (trans tyS (sym tyT))
```

### `⊑-object` cases

```agda
SchemaDriftSound (PrimitiveChanged primS _ _)
                 (⊑-object _ _ tyS _ _ _) =
                   prim≢object (subst IsPrimitive tyS primS)

SchemaDriftSound (ArrayItemDrift tyS _ _ _ _)
                 (⊑-object _ _ tyS' _ _ _) =
                   array≢object (trans (sym tyS) tyS')

SchemaDriftSound (RequiredFieldRemoved _ _ k∈ k∉)
                 (⊑-object _ _ _ _ _ r⊆) =
                   ∉-elim k∉ (All-∈ r⊆ k∈)

SchemaDriftSound (PropertyRemoved {s} {t} {k} _ _ lkO lkN)
                 (⊑-object _ _ _ _ pr _) =
                   search (Schema.properties s) pr lkO
                     where
                       search : ∀ ps → PropsRefine Schema⊑Co ps (Schema.properties t) → ¬ (lookupProp k ps ≢ nothing)

                       search [] _ lk = lk refl
                       search ((k' , _) :: ps) (hd , tl) lk with k ≟ k'
                       ... | no  _ = search ps tl lk
                       ... | yes refl = just≢nothing (trans (sym (fst (snd hd))) lkN)

SchemaDriftSound (PropertyDrift {s} {t} {k} {ti = ti} _ _ lkO lkN sd)
                 (⊑-object _ _ _ _ pr _) =
                   search (Schema.properties s) pr lkO
                     where
                       search : ∀ ps → PropsRefine Schema⊑Co ps (Schema.properties t) → ¬ (lookupProp k ps ≡ just _)
                       
                       search [] _ lk = ⊥-elim (just≢nothing (sym lk))
                       search ((k' , so) :: ps) (hd , tl) lk with k ≟ k'
                       ... | no  _ = search ps tl lk
                       ... | yes refl = SchemaDriftSound
                                          (subst
                                            (SchemaDrift so)
                                              (just-inj (trans (sym lkN) (fst (snd hd))))
                                              (subst (λ x → SchemaDrift x ti) (sym (just-inj lk)) sd))
                                          (snd (snd hd))

SchemaDriftSound (ShapeMismatch s≢t)
                 (⊑-object _ _ tyS tyT _ _) =
                   s≢t (trans tyS (sym tyT))
```

---

### 1.2. Endpoint Drift Soundness

```agda
EndpointDriftSound : ∀ {e₀ e₁} → EndpointDrift e₀ e₁ → ¬ Endpoint⊑ e₀ e₁

EndpointDriftSound (RouteChanged route≢)
                   (⊑-endpoint _ _ route≡ _ _ _ _) =
                     route≢ route≡

EndpointDriftSound (MethodChanged method≢)
                   (⊑-endpoint _ _ _ method≡ _ _ _) =
                     method≢ method≡

EndpointDriftSound {e₀} {e₁} (ParameterRemoved {ℓ = ℓ} {k = k} oldHas newMissing)
                             (⊑-endpoint _ _ _ _ (oldPres , _) _ _) =
                               helper (lookupParam ℓ k (Endpoint.parameters e₀)) refl
                                 where
                                   helper : ∀ res → lookupParam ℓ k (Endpoint.parameters e₀) ≡ res → ⊥

                                   helper nothing eq = ⊥-elim (oldHas eq)
                                   helper (just p) eq =
                                     let (p' , (lkNew , _)) = OldParamsPreserved-lookup oldPres eq
                                     in ⊥-elim (just≢nothing (trans (sym lkNew) newMissing))
          
EndpointDriftSound (RequiredParameterAdded {e₀} {p₀ = p₀} {p₁ = p₁} loc≡ name≡ lkOld lkNew oldFalse newTrue)
                   (⊑-endpoint _ _ _ _ (_ , newSafe) _ _) =
                     let (pOld , (lkOldFromSafe , reqOldFromSafe)) =
                           newSafe {Parameter.location p₁} {Parameter.name p₁} {p₁} lkNew newTrue

                         lkOldFromSafe' : lookupParam (Parameter.location p₀) (Parameter.name p₁) (Endpoint.parameters e₀) ≡ just pOld
                         lkOldFromSafe' = subst (λ ℓ → lookupParam ℓ (Parameter.name p₁) (Endpoint.parameters e₀) ≡ just pOld)
                                                (sym loc≡)
                                                lkOldFromSafe

                         lkOldFromSafe'' : lookupParam (Parameter.location p₀) (Parameter.name p₀) (Endpoint.parameters e₀) ≡ just pOld
                         lkOldFromSafe'' = subst (λ k → lookupParam (Parameter.location p₀) k (Endpoint.parameters e₀) ≡ just pOld)
                                                 (sym name≡)
                                                 lkOldFromSafe'

                         p₀≡pOld : p₀ ≡ pOld
                         p₀≡pOld = just-inj (trans (sym lkOld) lkOldFromSafe'')

                         reqP₀≡reqPOld : Parameter.required p₀ ≡ Parameter.required pOld
                         reqP₀≡reqPOld = cong Parameter.required p₀≡pOld

                         false≡true : false ≡ true
                         false≡true = trans (sym oldFalse)
                                           (trans reqP₀≡reqPOld reqOldFromSafe)

                     in false≢true false≡true

EndpointDriftSound (NewRequiredParameter {e₀} {e₁} {ℓ} {k} {p} oldMissing newHas reqTrue)
                   (⊑-endpoint _ _ _ _ (_ , newSafe) _ _) =
                     let (pOld , (lkOld , reqOld)) = newSafe {ℓ} {k} {p} newHas reqTrue
                     in just≢nothing (trans (sym lkOld) oldMissing)

EndpointDriftSound (ParameterSchemaChanged {e₀} {e₁} {p₀} {p₁} loc≡ name≡ lkOld lkNew schema≢)
                   (⊑-endpoint _ _ _ _ (oldPres , _) _ _) =
                     let
                       (pOld , (lkFromPres , paramRef)) =
                         OldParamsPreserved-lookup oldPres lkOld

                       lkNew₁ =
                         subst (λ ℓ →
                           lookupParam ℓ (Parameter.name p₁)
                             (Endpoint.parameters e₁) ≡ just p₁)
                           (sym loc≡) lkNew

                       lkNew₂ =
                         subst (λ k →
                           lookupParam (Parameter.location p₀) k
                             (Endpoint.parameters e₁) ≡ just p₁)
                           (sym name≡) lkNew₁

                       p₁≡pOld =
                         just-inj (trans (sym lkNew₂) lkFromPres)
                       (_ , (_ , (schemaEq , _))) = paramRef

                       schemaPOld≡schemaP₁ : Parameter.schema pOld ≡ Parameter.schema p₁
                       schemaPOld≡schemaP₁ = cong Parameter.schema (sym p₁≡pOld)

                       transported : Parameter.schema p₀ ≡ Parameter.schema p₁
                       transported = trans schemaEq schemaPOld≡schemaP₁
                     in
                       schema≢ transported

EndpointDriftSound (BodySchemaDrift bsOld bsNew sd)
                   (⊑-endpoint _ _ _ method≡ _ body⊑ _)
  with method≡
... | refl with bsOld | bsNew
...   | body-post  | body-post  = SchemaDriftSound sd body⊑
...   | body-put   | body-put   = SchemaDriftSound sd body⊑
...   | body-patch | body-patch = SchemaDriftSound sd body⊑

EndpointDriftSound (ResponseRemoved {e₀} {e₁} {st} oldHas newMissing)
                   (⊑-endpoint _ _ _ _ _ _ resps⊑) =
                     helper (lookupResp st (Endpoint.responses e₀)) refl
                       where
                         helper : ∀ res → lookupResp st (Endpoint.responses e₀) ≡ res → ⊥
                         helper nothing eq = oldHas eq
                         helper (just s) eq =
                           let (t , (lkNew , _)) = Resps⊑Co-lookup resps⊑ eq
                           in just≢nothing (trans (sym lkNew) newMissing)

EndpointDriftSound (ResponseDrift {e₀} {e₁} {st} {s₀} {s₁} lkOld lkNew sd)
                   (⊑-endpoint _ _ _ _ _ _ resps⊑) =
                     let (t , (lkNew' , s⊑t)) = Resps⊑Co-lookup resps⊑ lkOld
                     
                         s₁≡t : s₁ ≡ t
                         s₁≡t = just-inj (trans (sym lkNew) lkNew')
                         
                         sd' : SchemaDrift s₀ t
                         sd' = subst (SchemaDrift s₀) s₁≡t sd
                         
                     in SchemaDriftSound sd' s⊑t
```

---

### 1.3. API Drift Soundness

```agda
APIDriftSound : ∀ {a₀ a₁} → Drift a₀ a₁ → ¬ API⊑ a₀ a₁

APIDriftSound (ComponentRemoved {a₀} {a₁} {k} oldHas newMissing)
              (⊑-api _ _ comps⊑ _) =
                helper (lookupComponent k (API.components a₀)) refl
                  where
                    helper : ∀ res → lookupComponent k (API.components a₀) ≡ res → ⊥
                    helper nothing eq = oldHas eq
                    helper (just s) eq =
                      let (t , (lkNew , _)) = Components⊑-lookup comps⊑ eq
                      in just≢nothing (trans (sym lkNew) newMissing)

APIDriftSound (ComponentDriftWitness {a₀} {a₁} {k} {s₀} {s₁} lkOld lkNew sd)
              (⊑-api _ _ comps⊑ _) =
                let (t , (lkNew' , s₀⊑t)) = Components⊑-lookup comps⊑ lkOld
                    s₁≡t : s₁ ≡ t
                    s₁≡t = just-inj (trans (sym lkNew) lkNew')
                    
                    s₀⊑s₁ : Schema⊑Co s₀ s₁
                    s₀⊑s₁ = subst (Schema⊑Co s₀) (sym s₁≡t) s₀⊑t
                in SchemaDriftSound sd s₀⊑s₁
  
APIDriftSound (EndpointRemoved {a₀} {a₁} {r} {m} oldHas newMissing)
              (⊑-api _ _ _ paths⊑) =
                helper (lookupEndpoint r m (API.paths a₀)) refl
                where
                  helper : ∀ res → lookupEndpoint r m (API.paths a₀) ≡ res → ⊥
                  helper nothing eq = oldHas eq
                  helper (just e) eq =
                    let (e' , (lkNew , _)) = Endpoints⊑-lookup paths⊑ eq
                    in just≢nothing (trans (sym lkNew) newMissing)
      
APIDriftSound (EndpointDriftWitness {a₀} {a₁} {r} {m} {e₀} {e₁} lkOld lkNew ed)
              (⊑-api _ _ _ paths⊑) =
                let (e' , (lkNew' , e₀⊑e')) = Endpoints⊑-lookup paths⊑ lkOld
                    e₁≡e' : e₁ ≡ e'
                    e₁≡e' = just-inj (trans (sym lkNew) lkNew')

                    e₀⊑e₁ : Endpoint⊑ e₀ e₁
                    e₀⊑e₁ = subst (Endpoint⊑ e₀) (sym e₁≡e') e₀⊑e'
                in EndpointDriftSound ed e₀⊑e₁
```

---

### 1.4. Main Soundness Result

```agda
DriftSound : ∀ {a₀ a₁} → Drift a₀ a₁ → ¬ API⊑ a₀ a₁
DriftSound = APIDriftSound
```

---

## 2. Completeness

Refinement failure produces a drift witness. 

At each level, completeness follows directly from the corresponding decision procedure from `Semantics.DecidableRefinement`.

### 2.1. Schema Drift Completeness

```agda
SchemaDriftComplete :
  ∀ {s t}
  → WFSchema s
  → WFSchema t
  → ¬ Schema⊑Co s t
  → SchemaDrift s t

SchemaDriftComplete wfS wfT notRef
  with Schema⊑Co? wfS wfT
... | inl ref = ⊥-elim (notRef ref)
... | inr drift = drift
```

### 2.2. Endpoint Drift Completeness

```agda
EndpointDriftComplete :
  ∀ (e₀ e₁ : Endpoint)
  → WFEndpoint e₀
  → WFEndpoint e₁
  → ¬ Endpoint⊑ e₀ e₁
  → EndpointDrift e₀ e₁

EndpointDriftComplete e₀ e₁ wfE₀ wfE₁ notRef
  with Endpoint⊑? e₀ e₁ wfE₀ wfE₁
... | inl ref = ⊥-elim (notRef ref)
... | inr drift = drift
```

### 2.3. API Drift Completeness

```agda
DriftComplete :
  ∀ (a₀ a₁ : API)
  → WFAPI a₀
  → WFAPI a₁
  → ¬ API⊑ a₀ a₁
  → Drift a₀ a₁

DriftComplete a₀ a₁ wfA₀ wfA₁ notRef
  with API⊑? a₀ a₁ wfA₀ wfA₁
... | inl ref = ⊥-elim (notRef ref)
... | inr drift = drift
```

---

## 3. Drift and Refinement Failure

For well-formed APIs, drift is equivalent to refinement failure.

```agda
Drift-iff :
  ∀ (a₀ a₁ : API)
  → WFAPI a₀
  → WFAPI a₁
  → (Drift a₀ a₁ → ¬ API⊑ a₀ a₁) × (¬ API⊑ a₀ a₁ → Drift a₀ a₁)

Drift-iff a₀ a₁ wfA₀ wfA₁ = DriftSound , DriftComplete a₀ a₁ wfA₀ wfA₁
```
