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
open import Semantics.APIRefinement

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

  BodySchemaDrift :
      ∀ {e₀ e₁ s₀ s₁}
    → BodySchema (Endpoint.body e₀) s₀
    → BodySchema (Endpoint.body e₁) s₁
    → SchemaDrift s₀ s₁
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

API drift captures breaking changes at the level of whole specifications.

```agda
data Drift : API → API → Set where

  ComponentRemoved :
      ∀ {a₀ a₁ k}
    → lookupComponent k (API.components a₀) ≢ nothing
    → lookupComponent k (API.components a₁) ≡ nothing
    → Drift a₀ a₁

  ComponentDriftWitness :
      ∀ {a₀ a₁ k s₀ s₁}
    → lookupComponent k (API.components a₀) ≡ just s₀
    → lookupComponent k (API.components a₁) ≡ just s₁
    → SchemaDrift s₀ s₁
    → Drift a₀ a₁

  EndpointRemoved :
      ∀ {a₀ a₁ r m}
    → lookupEndpoint r m (API.paths a₀) ≢ nothing
    → lookupEndpoint r m (API.paths a₁) ≡ nothing
    → Drift a₀ a₁

  EndpointDriftWitness :
      ∀ {a₀ a₁ r m e₀ e₁}
    → lookupEndpoint r m (API.paths a₀) ≡ just e₀
    → lookupEndpoint r m (API.paths a₁) ≡ just e₁
    → EndpointDrift e₀ e₁
    → Drift a₀ a₁
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































------------------------------------------------ old -------------------------------------------------------------
### `⊑-prim` cases


SchemaDriftSound d
  (⊑-prim (wf-prim _ itemsS propsS reqS)
          (wf-prim _ _ _ _)
          _ _ eq) with d

... | PrimitiveChanged primS' primT' s≢t =
      s≢t eq

... | ArrayItemDrift _ _ itemsS' _ _ =
      ⊥-elim (just≢nothing (trans (sym itemsS') itemsS))

... | RequiredFieldRemoved {k = k} _ _ k∈ _ =
      ⊥-elim (∈-empty (subst (λ xs → k ∈ xs) reqS k∈))

... | PropertyRemoved {k = k} _ _ lkOld _ =
      lkOld (cong (lookupProp k) propsS)

... | PropertyDrift {k = k} _ _ lkOld _ _ =
      just≢nothing
        (trans (sym lkOld)
               (cong (lookupProp k) propsS))

### `⊑-array` cases


SchemaDriftSound d
  (⊑-array (wf-array typeS _ _ propsS reqS)
           (wf-array _ _ _ _ _)
           _ _ itemsS' itemsT' sub)
  with d

... | PrimitiveChanged primS primT s≢t =
      prim≢array (subst IsPrimitive typeS primS)

... | ArrayItemDrift _ _ itemsS₀ itemsT₀ drift =
      SchemaDriftSound
        (subst
          (SchemaDrift _)
          (just-inj (trans (sym itemsT₀) itemsT'))
          (subst
            (λ x → SchemaDrift x _)
            (just-inj (trans (sym itemsS₀) itemsS'))
            drift))
        sub

... | RequiredFieldRemoved {k = k} typeS' _ k∈ _ =
      ⊥-elim (∈-empty (subst (λ xs → k ∈ xs) reqS k∈))

... | PropertyRemoved {k = k} _ _ lkOld _ =
      lkOld (cong (lookupProp k) propsS)

... | PropertyDrift {k = k} _ _ lkOld _ _ =
      just≢nothing
        (trans (sym lkOld)
               (cong (lookupProp k) propsS))

### `⊑-object` cases

SchemaDriftSound d
  (⊑-object (wf-object typeS itemsS _ _ _ _)
            (wf-object _ _ _ _ _ _)
            _ _ propRef reqIncl)
  with d

... | PrimitiveChanged primS _ _ =
      prim≢object (subst IsPrimitive typeS primS)

... | ArrayItemDrift _ _ itemsS' _ _ =
      ⊥-elim (just≢nothing (trans (sym itemsS') itemsS))

... | RequiredFieldRemoved {k = k} _ _ k∈ k∉ =
      ∉-elim k∉ (All-∈ reqIncl k∈)

... | PropertyRemoved {s} {t} {k} _ _ lkOld lkNew =
      search (Schema.properties s) propRef lkOld
  where
    search : ∀ ps →  PropsRefine Schema⊑Co ps (Schema.properties t) → ¬ (lookupProp k ps ≢ nothing)
    
    search [] _ lk≢ =
      lk≢ refl

    search ((k' , _) :: ps) (hd , tl) lk≢
      with k ≟ k'

    ... | no _ =
          search ps tl lk≢

    ... | yes refl =
          let (_ , (lkNew≡just , _)) = hd
          in  just≢nothing (trans (sym lkNew≡just) lkNew)

... | PropertyDrift {s} {t} {k} {ti = ti} _ _ lkOld lkNew drift =
      search (Schema.properties s) propRef lkOld
  where
    search : ∀ ps → PropsRefine Schema⊑Co ps (Schema.properties t) → ¬ (lookupProp k ps ≡ just _)

    search [] _ lk = ⊥-elim (just≢nothing (sym lk))

    search ((k' , so) :: ps) (hd , tl) lk
      with k ≟ k'
      
    ... | no _ =
          search ps tl lk
          
    ... | yes refl =
          SchemaDriftSound
            (subst (SchemaDrift so)
                   (just-inj (trans (sym lkNew) (fst (snd hd))))
                   (subst (λ x → SchemaDrift x ti)
                          (sym (just-inj lk))
                          drift))
            (snd (snd hd))


