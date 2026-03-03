# Decidable Refinement

We show that refinement is decidable for well-formed specifications. More precisely, given two well-formed schemas, endpoints, or APIs, we can effectively decide whether the refinement relation holds.

The construction proceeds bottom-up. We first decide schema refinement by structural recursion on schema shape. We then lift this to endpoints, aligning parameters, request bodies, and responses using the schema decision procedure. Finally, we lift again to APIs by aligning components and endpoints via lookup.

All procedures are constructive and operate over finite structures. They rely only on decidable equality for syntactic identifiers and recursive checks on strictly smaller substructures.

Well-formedness is essential here. It guarantees uniqueness of keys and removes ambiguous lookup cases, ensuring that alignment is computable.

The result is an executable notion of compatibility: for any two well-formed APIs, we can decide whether one safely refines the other.

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
  using (⊑Co-refl; ⊑Co-trans; prim≢array; prim≢object)

open import Semantics.EndpointRefinement
open import Semantics.APIRefinement

open Σ using (fst ; snd)
```

---

## 1. Decidability of Covariant Schema Refinement

We decide covariant schema refinement by structural recursion on schema shape. The procedure mirrors the constructors of `Schema⊑Co`, with the object case requiring additional checks for property preservation and required-field inclusion.

---

### 1.1 Auxiliary List Decisions

### Decidable membership

```agda
_∈?_ : (x : String) → (xs : List String) → Dec (x ∈ xs)
_∈?_ x [] = no (λ ())
_∈?_ x (y :: ys) with x ≟ y
... | yes refl = yes here
... | no x≢y
    with x ∈? ys
...   | yes p  = yes (there p)
...   | no  np =
          no (λ {
            here      → x≢y refl
          ; (there q) → np q
          })
```

### Decidable subset

```agda
_⊆?_ : (xs ys : List String) → Dec (xs ⊆ ys)
_⊆?_ [] ys = yes all[]
_⊆?_ (x :: xs) ys
  with x ∈? ys
... | no x∉ys =
      no (λ {
        (all::_ px _) → x∉ys px
      })

... | yes x∈ys
    with xs ⊆? ys
...   | no xs⊈ys =
          no (λ {
            (all::_ _ rest) → xs⊈ys rest
          })
...   | yes xs⊆ys =
          yes (all::_ x∈ys xs⊆ys)
```

---

### 1.2 Decidable Property Refinement

To decide the object case of schema refinement, we check that every property in the old schema is present in the new schema with a refining type, by recursion over the old property list. The helper `lookupProp-wf` extracts a `WFSchema` witness for any schema retrieved by lookup, which is needed to make the recursive call to `Schema⊑Co?`.

`PropsRefine?` and `Schema⊑Co?` are declared `mutual` because object refinement requires calling `Schema⊑Co?` on property schemas, making the two definitions interdependent.

```agda
lookupProp-wf :
  ∀ {k s ps}
  → All WFSchema (values ps)
  → lookupProp k ps ≡ just s
  → WFSchema s
lookupProp-wf {k} {s} {[]} _ ()
lookupProp-wf {k} {s} {(k' , s') :: ps} (all::_ wfS wfRest) lk
  with k ≟ k'
... | yes refl = subst WFSchema (just-inj lk) wfS
... | no  _    = lookupProp-wf wfRest lk
```

```agda
mutual
  PropsRefine? :
      (ps qs : List (String × Schema))
    → All WFSchema (values ps)
    → All WFSchema (values qs)
    → Dec (PropsRefine Schema⊑Co ps qs)
  PropsRefine? [] qs _ _ = yes tt
  PropsRefine? ((k , s) :: ps) qs (all::_ wfS wfRest) wfQs
      with lookupProp k qs in eq
  ... | nothing = no (λ p → just≢nothing (sym (fst (snd (fst p)))))
  ... | just t
      with Schema⊑Co? wfS (lookupProp-wf wfQs eq)
  ... | no ¬r = no (λ p →
    let sn   = fst (fst p)
        lk   = fst (snd (fst p))
        r'   = snd (snd (fst p))
        sn≡t = sym (just-inj lk)
    in ¬r (subst (Schema⊑Co s) sn≡t r'))
  ... | yes r
    with PropsRefine? ps qs wfRest wfQs
  ... | no ¬rest = no (λ p → ¬rest (snd p))
  ... | yes rest = yes ((t , (refl , r)) , rest)
```

---

### 1.3 Decidable Covariant Schema Refinement

We decide refinement by structural case analysis on the well-formedness proofs of both schemas.

```agda
  Schema⊑Co? :
    ∀ {s t}
    → WFSchema s
    → WFSchema t
    → Dec (Schema⊑Co s t)
```

### Primitive cases

Primitive schemas refine only if their base types are equal. Cross-shape cases are
impossible by the shape equalities carried by the refinement constructors.

```agda
  Schema⊑Co? {s} {t}
    wfS@(wf-prim primS _ _ _)
    wfT@(wf-prim primT _ _ _)
    with Base≟ (Schema.type s) (Schema.type t)
  ... | yes refl =
        yes (⊑-prim wfS wfT primS primT refl)

  ... | no neq =
        no impossible
    where
      impossible : Schema⊑Co s t → ⊥
      impossible (⊑-prim _ _ _ _ eq) = neq eq
      impossible (⊑-array _ _ tyS _ _ _ _) =
        prim≢array (subst IsPrimitive tyS primS)
      impossible (⊑-object _ _ tyS _ _ _) =
        prim≢object (subst IsPrimitive tyS primS)

  Schema⊑Co? {s} {t}
    (wf-prim primS _ _ _)
    (wf-array tyT _ _ _ _) =
    no impossible
    where
      impossible : Schema⊑Co s t → ⊥

      impossible (⊑-prim _ _ _ _ eq) =
        prim≢array
          (subst IsPrimitive
            (trans eq tyT)
            primS)

      impossible (⊑-array _ _ tyS _ _ _ _) =
        prim≢array (subst IsPrimitive tyS primS)

      impossible (⊑-object _ _ tyS _ _ _) =
        prim≢object (subst IsPrimitive tyS primS)

  Schema⊑Co? {s} {t}
    (wf-prim primS _ _ _)
    (wf-object tyT _ _ _ _ _) =
    no impossible
    where
      impossible : Schema⊑Co s t → ⊥

      impossible (⊑-prim _ _ _ _ eq) =
        prim≢object
          (subst IsPrimitive
            (trans eq tyT)
            primS)

      impossible (⊑-array _ _ tyS _ _ _ _) =
        prim≢array (subst IsPrimitive tyS primS)

      impossible (⊑-object _ _ tyS _ _ _) =
        prim≢object (subst IsPrimitive tyS primS)
```

### Array cases

Array refinement is covariant in the item schema. Cross-shape cases are ruled out by incompatible type equalities.

```agda
  Schema⊑Co? {s} {t}
    wfS@(wf-array tyS itemsS wfItemS _ _)
    wfT@(wf-array tyT itemsT wfItemT _ _)
    with Schema⊑Co? wfItemS wfItemT
  ... | yes r =
        yes (⊑-array wfS wfT tyS tyT itemsS itemsT r)

  ... | no ¬r =
        no impossible
    where
      impossible : Schema⊑Co s t → ⊥

      impossible (⊑-prim _ _ primS' primT' _) =
        prim≢array (subst IsPrimitive tyS primS')

      impossible (⊑-object _ _ tyS' _ _ _) =
        array≢object (trans (sym tyS) tyS')

      impossible (⊑-array _ _ _ _ is it sub) =
        let
          si≡item  = just-inj (trans (sym is) itemsS)
          ti≡itemT = just-inj (trans (sym it) itemsT)

          sub₁ = subst (λ x → Schema⊑Co x _) si≡item sub
          sub₂ = subst (λ x → Schema⊑Co _ x) ti≡itemT sub₁
        in
          ¬r sub₂

  Schema⊑Co? {s} {t}
    (wf-array tyS _ _ _ _)
    (wf-prim primT _ _ _) =
    no impossible
    where
      impossible : Schema⊑Co s t → ⊥

      impossible (⊑-prim _ _ _ primT' eq) =
        prim≢array
          (subst IsPrimitive
            (trans (sym eq) tyS)
            primT')

      impossible (⊑-array _ _ _ tyT _ _ _) =
        prim≢array (subst IsPrimitive tyT primT)

      impossible (⊑-object _ _ _ tyT _ _) =
        prim≢object (subst IsPrimitive tyT primT)

  Schema⊑Co? {s} {t}
    (wf-array tyS _ _ _ _)
    (wf-object tyT _ _ _ _ _) =
    no impossible
    where
      impossible : Schema⊑Co s t → ⊥

      impossible (⊑-prim _ _ _ _ eq) =
        array≢object
          (trans
            (sym (trans (sym eq) tyS))
            tyT)

      impossible (⊑-array _ _ _ tyT' _ _ _) =
        array≢object (trans (sym tyT') tyT)

      impossible (⊑-object _ _ tyS' _ _ _) =
        array≢object (trans (sym tyS) tyS')
```

### Object cases

Object refinement requires:
1. Property refinement
2. Required-field subset

Cross-shape cases follow from contradictory type equalities.

```agda
  Schema⊑Co? {s} {t}
    wfS@(wf-object tyS itemsS wfPropsS wfReqS uniqS reqUniqS)
    wfT@(wf-object tyT itemsT wfPropsT wfReqT uniqT reqUniqT)
    with PropsRefine?
           (Schema.properties s)
           (Schema.properties t)
           wfPropsS
           wfPropsT
  ... | no ¬pr =
        no impossible₁
    where
      impossible₁ : Schema⊑Co s t → ⊥

      impossible₁ (⊑-object _ _ _ _ pr _) =
        ¬pr pr

      impossible₁ (⊑-prim _ _ primS' _ _) =
        prim≢object (subst IsPrimitive tyS primS')

      impossible₁ (⊑-array _ _ tyS' _ _ _ _) =
        array≢object (trans (sym tyS') tyS)

  ... | yes pr
    with Schema.required s ⊆? Schema.required t
  ...   | no ¬sub =
          no impossible₂
    where
      impossible₂ : Schema⊑Co s t → ⊥

      impossible₂ (⊑-object _ _ _ _ _ sub) =
        ¬sub sub

      impossible₂ (⊑-prim _ _ primS' _ _) =
        prim≢object (subst IsPrimitive tyS primS')

      impossible₂ (⊑-array _ _ tyS' _ _ _ _) =
        array≢object (trans (sym tyS') tyS)

  ...   | yes sub =
          yes (⊑-object wfS wfT tyS tyT pr sub)

  Schema⊑Co? {s} {t}
    (wf-object tyS _ _ _ _ _)
    (wf-prim primT _ _ _) =
    no impossible
    where
      impossible : Schema⊑Co s t → ⊥

      impossible (⊑-prim _ _ primS' _ _) =
        prim≢object (subst IsPrimitive tyS primS')

      impossible (⊑-array _ _ tyS' _ _ _ _) =
        array≢object (trans (sym tyS') tyS)

      impossible (⊑-object _ _ _ tyT' _ _) =
        prim≢object (subst IsPrimitive tyT' primT)

  Schema⊑Co? {s} {t}
    (wf-object tyS _ _ _ _ _)
    (wf-array  tyT _ _ _ _) =
    no impossible
    where
      impossible : Schema⊑Co s t → ⊥

      impossible (⊑-prim _ _ primS' _ _) =
        prim≢object (subst IsPrimitive tyS primS')

      impossible (⊑-array _ _ tyS' _ _ _ _) =
        array≢object (trans (sym tyS') tyS)

      impossible (⊑-object _ _ tyS' tyT' _ _) =
        array≢object (trans (sym tyT) tyT')
```

---

## 2. Decidability of Endpoint Refinement

Endpoint refinement reduces to alignment of parameters, request bodies, and responses. Since schema refinement is decidable, endpoint refinement is obtained by structural decomposition and finite lookup over components.

### 2.1 Decidable Parameter Refinement

```agda
ReqWeakens? : (old new : Bool) → Dec (ReqWeakens old new)
ReqWeakens? old false = yes (λ ())
ReqWeakens? true  true  = yes (λ _ → refl)
ReqWeakens? false true  = no (λ req → false≢true (req refl))
```

```agda
Param⊑Contra? : (p q : Parameter) → Dec (Param⊑Contra p q)
Param⊑Contra? p q
  with ParamLocation≟ (Parameter.location p) (Parameter.location q)
... | no ¬loc = no (λ r → ¬loc (fst r))
... | yes loc
  with Parameter.name p ≟ Parameter.name q
... | no ¬name = no (λ r → ¬name (fst (snd r)))
... | yes name
  with Base≟ (Parameter.schema p) (Parameter.schema q)
... | no ¬sch = no (λ r → ¬sch (fst (snd (snd r))))
... | yes sch
  with ReqWeakens? (Parameter.required p) (Parameter.required q)
... | no ¬req = no (λ r → ¬req (snd (snd (snd r))))
... | yes req = yes (loc , (name , (sch , req)))
```

```agda
OldParamsPreserved? : (old new : List Parameter) → Dec (OldParamsPreserved old new)
OldParamsPreserved? [] new = yes tt
OldParamsPreserved? (p :: ps) new
  with lookupParam (Parameter.location p) (Parameter.name p) new in lkeq
... | nothing =
      no (λ r →
        let
          lk = fst (snd (fst r))
        in
          just≢nothing (trans (sym lk) refl))

... | just q
  with Param⊑Contra? p q
... | no ¬r =
      no (λ r →
        let
          q'    = fst (fst r)
          lk    = fst (snd (fst r))
          pc    = snd (snd (fst r))
          q'≡q  = just-inj (trans (sym lk) refl)
        in
          ¬r (subst (Param⊑Contra p) q'≡q pc))

... | yes r
  with OldParamsPreserved? ps new
... | no ¬rest = no (λ r → ¬rest (snd r))
... | yes rest = yes ((q , (refl , r)) , rest)
```

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
```

```agda
Params⊑Contra? : (old new : List Parameter) → Unique (paramKeys new) → Dec (Params⊑Contra old new)
Params⊑Contra? old new uniq
  with OldParamsPreserved? old new
  | NewRequiredSafe? old new uniq
... | no ¬old | _       = no (λ r → ¬old (fst r))
... | yes old | no ¬new = no (λ r → ¬new (snd r))
... | yes old | yes new = yes (old , new)
```

---

### 2.2 Decidable Body Refinement

```agda
Body⊑Contra? : ∀ {m n} → (eq : m ≡ n) → (b₀ : Body m) → (b₁ : Body n) → WFBody b₀ → WFBody b₁ → Dec (Body⊑Contra eq b₀ b₁)
Body⊑Contra? refl NoBody       NoBody       _                _                = yes tt
Body⊑Contra? refl NoBodyD      NoBodyD      _                _                = yes tt
Body⊑Contra? refl (HasBody  s) (HasBody  t) (wf-hasBody  ws) (wf-hasBody  wt) = Schema⊑Co? wt ws
Body⊑Contra? refl (HasBodyU s) (HasBodyU t) (wf-hasBodyU ws) (wf-hasBodyU wt) = Schema⊑Co? wt ws
Body⊑Contra? refl (HasBodyP s) (HasBodyP t) (wf-hasBodyP ws) (wf-hasBodyP wt) = Schema⊑Co? wt ws
```

---

### 2.3 Decidable Response Refinement

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
Resps⊑Co? : (old new : List Response) → All WFResponse old → All WFResponse new → Dec (Resps⊑Co old new)
Resps⊑Co? [] new _ _ = yes tt
Resps⊑Co? (response st s :: rs) new
  (all::_ (wf-response wfS) wfRs)
  wfNew
  with lookupResp st new in lkeq
... | nothing =
      no λ r →
        let (t , (lk , _)) = fst r
        in just≢nothing (sym lk)
... | just t
  with Schema⊑Co? wfS (lookupResp-wf wfNew lkeq)
  | Resps⊑Co? rs new wfRs wfNew
... | no ¬sch | _ =
      no λ r →
        let (t' , (lk' , sch)) = fst r
            t≡t' = just-inj (sym lk')
        in ¬sch (subst (Schema⊑Co s) t≡t' sch)
... | yes sch | no ¬tail = no λ r → ¬tail (snd r)
... | yes sch | yes tail = yes ((t , (refl , sch)) , tail)
```

---

### 2.4 Decidable Endpoint Refinement

```agda
wfEndpoint-paramUniq : ∀ {e} → WFEndpoint e → Unique (paramKeys (Endpoint.parameters e))
wfEndpoint-paramUniq (wf-endpoint _ _ uniq _ _ _) = uniq

wfEndpoint-body : ∀ {e} → WFEndpoint e → WFBody (Endpoint.body e)
wfEndpoint-body (wf-endpoint _ _ _ body _ _) = body

wfEndpoint-resps : ∀ {e} → WFEndpoint e → All WFResponse (Endpoint.responses e)
wfEndpoint-resps (wf-endpoint _ _ _ _ resps _) = resps
```

```agda
Endpoint⊑? : (eOld eNew : Endpoint) → WFEndpoint eOld → WFEndpoint eNew → Dec (Endpoint⊑ eOld eNew)
Endpoint⊑? eOld eNew wfOld wfNew
  with Path≟ (Endpoint.route eOld) (Endpoint.route eNew)
... | no ¬route = no (λ { (⊑-endpoint _ _ route≡ _ _ _ _) → ¬route route≡ })
... | yes route≡
  with Method≟ (Endpoint.method eOld) (Endpoint.method eNew)
... | no ¬method = no (λ { (⊑-endpoint _ _ _ method≡ _ _ _) → ¬method method≡ })
... | yes refl
  with Params⊑Contra? (Endpoint.parameters eOld) (Endpoint.parameters eNew) (wfEndpoint-paramUniq wfNew)
... | no ¬params = no (λ { (⊑-endpoint _ _ _ _ params _ _) → ¬params params })
... | yes params
  with Body⊑Contra? refl (Endpoint.body eOld) (Endpoint.body eNew)
                         (wfEndpoint-body wfOld) (wfEndpoint-body wfNew)
... | no ¬body =
    no (λ { (⊑-endpoint _ _ _ refl _ body _) → ¬body body })
... | yes body
  with Resps⊑Co? (Endpoint.responses eOld) (Endpoint.responses eNew)
                 (wfEndpoint-resps wfOld) (wfEndpoint-resps wfNew)
... | no ¬resps = no (λ { (⊑-endpoint _ _ _ _ _ _ resps) → ¬resps resps })
... | yes resps = yes (⊑-endpoint wfOld wfNew route≡ refl params body resps)
```

---

## 3. Decidability of API Refinement

We now lift refinement decidability to the level of whole APIs. Since schema and endpoint refinement are already decidable, API refinement reduces to finite alignment of components and endpoints via lookup, followed by recursive checks on matched entries. As before, well-formedness guarantees uniqueness of keys, ensuring that alignment is computable and unambiguous.

### 3.1 Decidable Component Refinement

```agda
lookupComponent-wf : ∀ {k s cs} → All WFSchema (values cs) → lookupComponent k cs ≡ just s → WFSchema s
lookupComponent-wf {k} {cs = []} _ ()
lookupComponent-wf {k} {cs = (k' , s') :: cs} (all::_ wfS rest) lk
  with k ≟ k'
... | yes refl = subst WFSchema (just-inj lk) wfS
... | no  _    = lookupComponent-wf rest lk
```

```agda
Components⊑? : (old new : List (String × Schema)) → All WFSchema (values old) → All WFSchema (values new) → Dec (Components⊑ old new)
Components⊑? [] new _ _ = yes tt
Components⊑? ((k , s) :: cs) new (all::_ wfS wfRest) wfNew
  with lookupComponent k new in lkeq
... | nothing = no λ r → just≢nothing (sym (fst (snd (fst r))))
... | just t

  with Schema⊑Co? wfS (lookupComponent-wf wfNew lkeq)
  | Components⊑? cs new wfRest wfNew  
... | no ¬sch | _ = no λ r →
      let (t' , (lk' , sch)) = fst r
          t≡t' = just-inj (sym lk')
      in ¬sch (subst (Schema⊑Co s) t≡t' sch)
... | yes sch | no ¬rest = no λ r → ¬rest (snd r)
... | yes sch | yes rest = yes ((t , (refl , sch)) , rest)
```

---

### 3.2 Decidable Endpoint List Refinement


```agda
lookupEndpoint-wf : ∀ {r m e es} → All WFEndpoint es → lookupEndpoint r m es ≡ just e → WFEndpoint e
lookupEndpoint-wf {r} {m} {e} {[]} _ ()
lookupEndpoint-wf {r} {m} {e} {h :: es} (all::_ wfH wfRest) lk
  with Path≟ r (Endpoint.route h)
... | no _ = lookupEndpoint-wf wfRest lk
... | yes refl
  with Method≟ m (Endpoint.method h)
...   | no _ = lookupEndpoint-wf wfRest lk
...   | yes refl = subst WFEndpoint (just-inj lk) wfH
```

```agda
Endpoints⊑? : (old new : List Endpoint) → All WFEndpoint old → All WFEndpoint new → Dec (Endpoints⊑ old new)
Endpoints⊑? [] new _ _ = yes tt
Endpoints⊑? (e :: es) new (all::_ wfE wfRest)
  wfNew
  with lookupEndpoint
         (Endpoint.route e)
         (Endpoint.method e)
         new
         in lkeq

... | nothing =
    no λ r →
      let (e' , (lk , _)) = fst r
      in just≢nothing (sym lk)

... | just e'
  with Endpoint⊑? e e' wfE (lookupEndpoint-wf wfNew lkeq)
  | Endpoints⊑? es new wfRest wfNew

... | no ¬ep | _ =
    no λ r →
      let (e'' , (lk' , ep)) = fst r
          e''≡e' = just-inj (sym lk')
      in ¬ep (subst (Endpoint⊑ e) e''≡e' ep)

... | yes ep | no ¬rest =
    no λ r → ¬rest (snd r)

... | yes ep | yes rest =
    yes ((e' , (refl , ep)) , rest)
```

---

### 3.3 Decidable API Refinement

```agda
wfAPI-components : ∀ {a} → WFAPI a → All WFSchema (values (API.components a))
wfAPI-components (wf-api wfComps _ _ _) = wfComps

wfAPI-paths : ∀ {a} → WFAPI a → All WFEndpoint (API.paths a)
wfAPI-paths (wf-api _ _ wfPaths _) = wfPaths
```

```agda
API⊑? : (aOld aNew : API) → WFAPI aOld → WFAPI aNew → Dec (API⊑ aOld aNew)
API⊑? aOld aNew wfOld wfNew
  with Components⊑?
         (API.components aOld)
         (API.components aNew)
         (wfAPI-components wfOld)
         (wfAPI-components wfNew)

... | no ¬comps =
      no (λ { (⊑-api _ _ comps _) → ¬comps comps })

... | yes comps
  with Endpoints⊑?
         (API.paths aOld)
         (API.paths aNew)
         (wfAPI-paths wfOld)
         (wfAPI-paths wfNew)

... | no ¬eps =
      no (λ { (⊑-api _ _ _ eps) → ¬eps eps })

... | yes eps =
      yes (⊑-api wfOld wfNew comps eps)
```
