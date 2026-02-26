# Drift

So far we have focused on showing when one API safely refines another. Refinement gives positive evidence that a change preserves the original contract.

Drift looks at the same situation from the other side. Instead of proving that evolution is safe, we isolate concrete ways in which it can fail. A drift witness identifies a specific structural guarantee that has been broken. For example, an endpoint being removed, a required field being introduced, or a response type being narrowed.

The aim here is not just to say that two APIs are incompatible, but to explain why. To keep this systematic, drift follows the same layered structure as refinement: we first describe breaking changes at the level of schemas, then lift them to endpoints, and finally to entire APIs.

The key result of this section is that any such witness of drift rules out refinement. In other words, incompatibility in this model always has a structural explanation.

```agda
module Semantics.Drift where

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

open Σ using (fst ; snd)
```

---

## 1. Schema Drift

Schema drift captures breaking changes inside schemas. Each constructor corresponds to a structural obligation required by schema refinement that can fail.

```agda
data SchemaDrift : Schema → Schema → Set where

  PrimitiveChanged :
      ∀ {s t}
    → IsPrimitive (Schema.type s)
    → IsPrimitive (Schema.type t)
    → Schema.type s ≢ Schema.type t
    → SchemaDrift s t

  ArrayItemDrift :
      ∀ {s t si ti}
    → Schema.type s ≡ array
    → Schema.type t ≡ array
    → Schema.items s ≡ just si
    → Schema.items t ≡ just ti
    → SchemaDrift si ti
    → SchemaDrift s t

  RequiredFieldRemoved :
      ∀ {s t k}
    → Schema.type s ≡ object
    → Schema.type t ≡ object
    → k ∈ Schema.required s
    → k ∉ Schema.required t
    → SchemaDrift s t

  PropertyRemoved :
      ∀ {s t k}
    → Schema.type s ≡ object
    → Schema.type t ≡ object
    → lookupProp k (Schema.properties s) ≢ nothing
    → lookupProp k (Schema.properties t) ≡ nothing
    → SchemaDrift s t

  PropertyDrift :
      ∀ {s t k si ti}
    → Schema.type s ≡ object
    → Schema.type t ≡ object
    → lookupProp k (Schema.properties s) ≡ just si
    → lookupProp k (Schema.properties t) ≡ just ti
    → SchemaDrift si ti
    → SchemaDrift s t
```

## 2. Endpoint Drift

Endpoint drift captures breaking changes at the level of individual operations.

Each constructor corresponds to a refinement obligation at the endpoint level that can fail.

```agda
data BodySchema : ∀ {m} → Body m → Schema → Set where
  body-post  : ∀ {s} → BodySchema (HasBody  s) s
  body-put   : ∀ {s} → BodySchema (HasBodyU s) s
  body-patch : ∀ {s} → BodySchema (HasBodyP s) s
  
data EndpointDrift : Endpoint → Endpoint → Set where

  RouteChanged :
      ∀ {e₀ e₁}
    → Endpoint.route e₀ ≢ Endpoint.route e₁
    → EndpointDrift e₀ e₁

  MethodChanged :
      ∀ {e₀ e₁}
    → Endpoint.method e₀ ≢ Endpoint.method e₁
    → EndpointDrift e₀ e₁

  ParameterRemoved :
      ∀ {e₀ e₁ ℓ k}
    → lookupParam ℓ k (Endpoint.parameters e₀) ≢ nothing
    → lookupParam ℓ k (Endpoint.parameters e₁) ≡ nothing
    → EndpointDrift e₀ e₁

  RequiredParameterAdded :
      ∀ {e₀ e₁ p₀ p₁}
    → Parameter.location p₀ ≡ Parameter.location p₁
    → Parameter.name p₀ ≡ Parameter.name p₁
    → lookupParam (Parameter.location p₀)
                  (Parameter.name p₀)
                  (Endpoint.parameters e₀)
        ≡ just p₀
    → lookupParam (Parameter.location p₁)
                  (Parameter.name p₁)
                  (Endpoint.parameters e₁)
        ≡ just p₁
    → Parameter.required p₀ ≡ false
    → Parameter.required p₁ ≡ true
    → EndpointDrift e₀ e₁

  NewRequiredParameter :
       ∀ {e₀ e₁ ℓ k p}
     → lookupParam ℓ k (Endpoint.parameters e₀) ≡ nothing
     → lookupParam ℓ k (Endpoint.parameters e₁) ≡ just p
     → Parameter.required p ≡ true
     → EndpointDrift e₀ e₁

  ParameterSchemaChanged :
      ∀ {e₀ e₁ p₀ p₁}
    → Parameter.location p₀ ≡ Parameter.location p₁
    → Parameter.name p₀ ≡ Parameter.name p₁
    → lookupParam (Parameter.location p₀)
                  (Parameter.name p₀)
                  (Endpoint.parameters e₀)
        ≡ just p₀
    → lookupParam (Parameter.location p₁)
                  (Parameter.name p₁)
                  (Endpoint.parameters e₁)
        ≡ just p₁
    → Parameter.schema p₀ ≢ Parameter.schema p₁
    → EndpointDrift e₀ e₁

  BodySchemaDrift :
      ∀ {e₀ e₁ s₀ s₁}
    → BodySchema (Endpoint.body e₀) s₀
    → BodySchema (Endpoint.body e₁) s₁
    → SchemaDrift s₁ s₀
    → EndpointDrift e₀ e₁

  ResponseRemoved :
      ∀ {e₀ e₁ st}
    → lookupResp st (Endpoint.responses e₀) ≢ nothing
    → lookupResp st (Endpoint.responses e₁) ≡ nothing
    → EndpointDrift e₀ e₁

  ResponseDrift :
      ∀ {e₀ e₁ st s₀ s₁}
    → lookupResp st (Endpoint.responses e₀) ≡ just s₀
    → lookupResp st (Endpoint.responses e₁) ≡ just s₁
    → SchemaDrift s₀ s₁
    → EndpointDrift e₀ e₁
```

---

## 3. API Drift

API drift captures breaking changes at the level of whole
specifications.

```agda
data Drift : API → API → Set where

  ComponentRemoved : ∀ {a₀ a₁ k} → lookupComponent k (API.components
      a₀) ≢ nothing → lookupComponent k (API.components a₁) ≡ nothing
      → Drift a₀ a₁

  ComponentDriftWitness : ∀ {a₀ a₁ k s₀ s₁} → lookupComponent k
      (API.components a₀) ≡ just s₀ → lookupComponent k
      (API.components a₁) ≡ just s₁ → SchemaDrift s₀ s₁ → Drift a₀ a₁

  EndpointRemoved : ∀ {a₀ a₁ r m} → lookupEndpoint r m (API.paths a₀)
      ≢ nothing → lookupEndpoint r m (API.paths a₁) ≡ nothing → Drift
      a₀ a₁

  EndpointDriftWitness : ∀ {a₀ a₁ r m e₀ e₁} → lookupEndpoint r m
      (API.paths a₀) ≡ just e₀ → lookupEndpoint r m (API.paths a₁) ≡
      just e₁ → EndpointDrift e₀ e₁ → Drift a₀ a₁
```

At this point we have a concrete structural account of breaking change. Drift follows the same layered organisation as refinement, starting from schemas and lifting through endpoints to whole APIs.

The remaining task is to connect this back to refinement itself. Intuitively, if we can exhibit a specific structural violation, then the new API cannot refine the old one. The next theorem makes that connection precise.

---

## 4. Drift Theorem (Soundness of Drift)

The central result of this section is that drift genuinely captures incompatibility. If a concrete structural violation can be exhibited, then refinement cannot hold.

We establish this in three stages, mirroring the layered definition of drift. First we show that schema drift contradicts schema refinement. We then lift this argument to endpoints, and finally to entire APIs.

---

### 4.1 Schema drift refutes schema refinement

The proof proceeds by structural case analysis on both the drift witness and the refinement derivation. In each branch, either we derive a direct semantic contradiction (for example, a changed primitive type contradicting primitive refinement), or we eliminate an impossible shape combination using the well-formedness invariants enforced by the refinement constructors.

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
```

---

### 4.2 Endpoint drift refutes endpoint refinement

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

                         -- rewrite the lookup using location equality
                         lkOldFromSafe' : lookupParam (Parameter.location p₀) (Parameter.name p₁) (Endpoint.parameters e₀) ≡ just pOld
                         lkOldFromSafe' = subst (λ ℓ → lookupParam ℓ (Parameter.name p₁) (Endpoint.parameters e₀) ≡ just pOld)
                                                (sym loc≡)
                                                lkOldFromSafe

                         -- rewrite using name equality
                         lkOldFromSafe'' : lookupParam (Parameter.location p₀) (Parameter.name p₀) (Endpoint.parameters e₀) ≡ just pOld
                         lkOldFromSafe'' = subst (λ k → lookupParam (Parameter.location p₀) k (Endpoint.parameters e₀) ≡ just pOld)
                                                 (sym name≡)
                                                 lkOldFromSafe'

                         -- the two lookups must find the same parameter
                         p₀≡pOld : p₀ ≡ pOld
                         p₀≡pOld = just-inj (trans (sym lkOld) lkOldFromSafe'')

                         -- extract the required field from the equality
                         reqP₀≡reqPOld : Parameter.required p₀ ≡ Parameter.required pOld
                         reqP₀≡reqPOld = cong Parameter.required p₀≡pOld

                         -- this gives us a contradiction: p₀.required = false but also = true
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

                       -- rewrite lkNew to p₀ key
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

### 4.3 API drift refutes API refinement

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

### 4.4 Drift and incompatibility

Drift was introduced as a structural account of breaking change.
Each constructor isolates a specific refinement obligation that may fail: a removed component, a strengthened parameter, a narrowed response schema, or a body that becomes too restrictive.

The previous sections established soundness at every layer:

- schema drift refutes schema refinement,
- endpoint drift refutes endpoint refinement,
- API drift refutes API refinement.

These results compose directly. At the top level, we obtain:

```agda
DriftSound : ∀ {a₀ a₁} → Drift a₀ a₁ → ¬ API⊑ a₀ a₁
DriftSound = APIDriftSound
```

This theorem states that incompatibility in the model is never arbitrary.
If refinement fails, it is *because&* some concrete structural guarantee has been violated. Drift provides that witness.


At this point, we have a complete semantic account of breaking evolution:

- refinement captures safe change,
- drift captures structural violation,
- and drift soundness ensures the two are mutually exclusive.
