# Decidable Well-Formedness

This module gives executable decision procedures for all well-formedness judgements defined in `WellFormed.Core`. Each checker returns either a positive proof of well-formedness or a structured ill-formedness witness from `WellFormed.IllFormed`.

```agda
module WellFormed.Decidable where

open import Prelude
open import Syntax.Syntax
open import Syntax.Decidable

open import WellFormed.Core
open import WellFormed.IllFormed
```

## 1. Schema Well-Formedness

The checker follows the three schema shapes from `WFSchema`:

- primitive: array/object-only fields are empty,
- array: `items` exists and is well-formed, object-only fields are empty,
- object: no `items`, all properties well-formed, all required names scoped to properties, unique property keys, unique required names.

The implementation is split into one named helper per shape, all declared in a
single `mutual` block. `array-case` and `object-case` recurse into `WFSchema?`
for nested schemas; `AllWFProps?` calls `WFSchema?` on each property value.
`WFSchema?` itself is then a flat dispatcher that reads the type tag and delegates.

### 1.1 Shared utilities

```agda
HasDuplicate? : ∀ {A} → ((x y : A) → Dec (x ≡ y)) → (xs : List A) → Unique xs ∔ HasDuplicate xs
HasDuplicate? eq [] = inl uniq[]
HasDuplicate? eq (x :: xs) with ∈?-gen eq x xs
... | yes x∈xs = inr (dup-here x∈xs)
... | no  x∉xs with HasDuplicate? eq xs
...   | inr dup    = inr (dup-there dup)
...   | inl uniqXs = inl (uniq::_ (∉-intro-gen eq x∉xs) uniqXs)
```

### 1.2 Internal witness type for property checking

`BadProp ps` records the first property in `ps` whose schema is ill-formed,
together with a membership proof locating it in the list.

```agda
data BadProp : List (String × Schema) → Set where
  bad-prop :
    ∀ {ps}
    → (k : String)
    → (child : Schema)
    → (k , child) ∈ ps
    → SchemaIllFormed child
    → BadProp ps
```

### 1.3 The decision procedures

```agda
mutual

  -- Primitive helper
  primitive-case :
    (s : Schema)
    → IsPrimitive (Schema.type s)
    → WFSchema s ∔ SchemaIllFormed s
  primitive-case s prim
    with Schema.items s in itemsEq
  ... | just _  = inr (prim-has-items prim itemsEq)
  ... | nothing
    with Schema.properties s in propsEq
  ...   | (k , child) :: _ =
            inr (prim-has-properties prim k child
              (subst ((k , child) ∈_) (sym propsEq) here))
  ...   | []
      with Schema.required s in reqEq
  ...     | k :: _ =
              inr (prim-has-required prim k
                (subst (k ∈_) (sym reqEq) here))
  ...     | [] = inl (wf-prim prim itemsEq propsEq reqEq)

  -- Array helper
  array-case :
    (s : Schema)
    → Schema.type s ≡ array
    → WFSchema s ∔ SchemaIllFormed s
  array-case s tyEq
    with Schema.items s in itemsEq
  ... | nothing = inr (array-missing-items tyEq itemsEq)
  ... | just item
    with WFSchema? item
  ...   | inr illItem = inr (array-item-ill-formed tyEq itemsEq illItem)
  ...   | inl wfItem
      with Schema.properties s in propsEq
  ...     | (k , child) :: _ =
              inr (array-has-properties tyEq k child
                (subst ((k , child) ∈_) (sym propsEq) here))
  ...     | []
        with Schema.required s in reqEq
  ...       | k :: _ =
                inr (array-has-required tyEq k
                  (subst (k ∈_) (sym reqEq) here))
  ...       | [] = inl (wf-array tyEq itemsEq wfItem propsEq reqEq)

  -- Object helper
  object-case :
    (s : Schema)
    → Schema.type s ≡ object
    → WFSchema s ∔ SchemaIllFormed s
  object-case s tyEq
    with Schema.items s in itemsEq
  ... | just _  = inr (object-has-items tyEq itemsEq)
  ... | nothing
    with AllWFProps? (Schema.properties s)
  ...   | inr (bad-prop k child k∈props illChild) =
            inr (object-property-ill-formed tyEq k child k∈props illChild)
  ...   | inl propsWF
      with Schema.required s ⊆? keys (Schema.properties s)
  ...     | no ¬req⊆keys =
              let (k , (k∈req , k∉keys)) = ⊆-counterexample ¬req⊆keys
              in  inr (object-missing-required tyEq k k∈req k∉keys)
  ...     | yes req⊆keys
        with HasDuplicate? _≟_ (keys (Schema.properties s))
  ...       | inr dupKeys = inr (object-duplicate-properties tyEq dupKeys)
  ...       | inl uniqKeys
          with HasDuplicate? _≟_ (Schema.required s)
  ...         | inr dupReq  = inr (object-duplicate-required tyEq dupReq)
  ...         | inl uniqReq =
                  inl (wf-object tyEq itemsEq propsWF req⊆keys uniqKeys uniqReq)

  -- Property list checker
  AllWFProps? :
    (ps : List (String × Schema))
    → All WFSchema (values ps) ∔ BadProp ps
  AllWFProps? [] = inl all[]
  AllWFProps? ((k , child) :: ps)
    with WFSchema? child
  ... | inr illChild = inr (bad-prop k child here illChild)
  ... | inl wfChild
    with AllWFProps? ps
  ...   | inl rest = inl (all::_ wfChild rest)
  ...   | inr (bad-prop k' child' k'∈tail illChild') =
            inr (bad-prop k' child' (there k'∈tail) illChild')

```

### 1.4 Main Schema Dispatcher

```agda
  WFSchema? : (s : Schema) → WFSchema s ∔ SchemaIllFormed s
  WFSchema? s with Schema.type s in tyEq
  ... | integer = primitive-case s (subst IsPrimitive (sym tyEq) prim-integer)
  ... | string  = primitive-case s (subst IsPrimitive (sym tyEq) prim-string)
  ... | boolean = primitive-case s (subst IsPrimitive (sym tyEq) prim-boolean)
  ... | number  = primitive-case s (subst IsPrimitive (sym tyEq) prim-number)
  ... | array   = array-case  s tyEq
  ... | object  = object-case s tyEq
```

---

## 2. Parameter Well-Formedness

`WFParameter?` branches on the parameter's location. Path parameters must be required and primitive; query parameters only need to be primitive.

The `no` branch of `IsPrimitive?` gives `¬ IsPrimitive b`, but `param-nonprimitive` expects a `NonPrimitive` witness. The small lemma `nonprim-from` bridges the two by exhausting the primitive cases with `⊥-elim` and returning the appropriate constructor for `object` and `array`.

### 2.1 Shared utility

The `no` branch of `IsPrimitive?` gives `¬ IsPrimitive b`, but
`param-nonprimitive` expects a `NonPrimitive` witness. `nonprim-from` bridges
the two by exhausting the primitive cases with `⊥-elim` and returning the
appropriate constructor for `object` and `array`.

```agda
nonprim-from : ∀ {b} → ¬ IsPrimitive b → NonPrimitive b
nonprim-from {array}   _  = nonprim-array
nonprim-from {object}  _  = nonprim-object
nonprim-from {integer} ¬p = ⊥-elim (¬p prim-integer)
nonprim-from {string}  ¬p = ⊥-elim (¬p prim-string)
nonprim-from {boolean} ¬p = ⊥-elim (¬p prim-boolean)
nonprim-from {number}  ¬p = ⊥-elim (¬p prim-number)
```

### 2.2 Location case helpers

Each location gets its own helper so that the `...` notation in `WFParameter?` is never ambiguous.

```agda
query-case : (p : Parameter) → Parameter.location p ≡ query → WFParameter p ∔ ParameterIllFormed p
query-case p locEq with IsPrimitive? (Parameter.schema p)
... | yes prim = inl (wf-query-param locEq prim)
... | no ¬prim = inr (param-nonprimitive (nonprim-from ¬prim))
```

```agda
path-case : (p : Parameter) → Parameter.location p ≡ path → WFParameter p ∔ ParameterIllFormed p
path-case p locEq with Parameter.required p in reqEq
... | false = inr (path-param-not-required locEq reqEq)
... | true
  with IsPrimitive? (Parameter.schema p)
...   | yes prim = inl (wf-path-param locEq reqEq prim)
...   | no ¬prim = inr (param-nonprimitive (nonprim-from ¬prim))
```

### 2.3 Main parameter dispatcher

```agda
WFParameter? : (p : Parameter) → WFParameter p ∔ ParameterIllFormed p
WFParameter? p with Parameter.location p in locEq
... | query = query-case p locEq
... | path  = path-case  p locEq
```

---

## 3. Path Well-Formedness

`WFPath?` checks the three obligations from `WFPath` in order: placeholders
are unique, every placeholder is declared as a path parameter, and every path
parameter appears as a placeholder.

```agda
WFPath? : (p : Path) (ps : List Parameter) → WFPath p ps ∔ PathIllFormed p ps
WFPath? p ps
  with HasDuplicate? _≟_ (pathPlaceholders p)
... | inr dup = inr (duplicate-placeholder dup)
... | inl uniq
  with pathPlaceholders p ⊆? pathParamNames ps
... | no ¬sub =
        let (x , (x∈ph , x∉pa)) = ⊆-counterexample ¬sub
        in  inr (placeholder-not-declared x x∈ph x∉pa)
... | yes ph⊆pa
  with pathParamNames ps ⊆? pathPlaceholders p
... | no ¬sub =
        let (x , (x∈pa , x∉ph)) = ⊆-counterexample ¬sub
        in  inr (orphan-path-parameter x x∈pa x∉ph)
... | yes pa⊆ph = inl (wf-path uniq ph⊆pa pa⊆ph)
```

---

## 4. Body Well-Formedness

`WFBody?` pattern matches directly on the body constructor. `NoBody` and `NoBodyD` are unconditionally well-formed. The three schema-carrying cases delegate to `WFSchema?` and lift the result into the appropriate `BodyIllFormed` constructor on failure.

```agda
WFBody? : ∀ {m} → (b : Body m) → WFBody b ∔ BodyIllFormed b
WFBody? NoBody       = inl wf-nobody
WFBody? NoBodyD      = inl wf-nobodyD
WFBody? (HasBody  s) with WFSchema? s
... | inl wf  = inl (wf-hasBody  wf)
... | inr ill = inr (post-body-ill-formed  ill)
WFBody? (HasBodyU s) with WFSchema? s
... | inl wf  = inl (wf-hasBodyU wf)
... | inr ill = inr (put-body-ill-formed   ill)
WFBody? (HasBodyP s) with WFSchema? s
... | inl wf  = inl (wf-hasBodyP wf)
... | inr ill = inr (patch-body-ill-formed ill)
```

---

## 5. Response Well-Formedness

`WFResponse?` is the simplest checker: a response is just a status code paired with a schema, so well-formedness reduces to a single `WFSchema?` call.

```agda
WFResponse? : (r : Response) → WFResponse r ∔ ResponseIllFormed r
WFResponse? (response st s) with WFSchema? s
... | inl wf  = inl (wf-response wf)
... | inr ill = inr (response-schema-ill-formed ill)
```

---

## 6. Endpoint Well-Formedness

`WFEndpoint?` works through the six obligations from `wf-endpoint` in order, returning the first failure it finds.

### 6.1 Internal witness types and list checkers

`BadParam` and `BadResponse` mirror `BadProp` from section 1: each records the first offending list element together with its membership proof, so the result can be fed directly into the endpoint ill-formedness constructors.

```agda
data BadParam : List Parameter → Set where
  bad-param :
    ∀ {ps}
    → (p : Parameter)
    → p ∈ ps
    → ParameterIllFormed p
    → BadParam ps

data BadResponse : List Response → Set where
  bad-response :
    ∀ {rs}
    → (r : Response)
    → r ∈ rs
    → ResponseIllFormed r
    → BadResponse rs
```

```agda
AllWFParams? : (ps : List Parameter) → All WFParameter ps ∔ BadParam ps
AllWFParams? [] = inl all[]
AllWFParams? (p :: ps) with WFParameter? p
... | inr ill = inr (bad-param p here ill)
... | inl wf
  with AllWFParams? ps
...   | inl rest = inl (all::_ wf rest)
...   | inr (bad-param p' p'∈tail ill') = inr (bad-param p' (there p'∈tail) ill')

AllWFResponses? : (rs : List Response) → All WFResponse rs ∔ BadResponse rs
AllWFResponses? [] = inl all[]
AllWFResponses? (r :: rs) with WFResponse? r
... | inr ill = inr (bad-response r here ill)
... | inl wf
  with AllWFResponses? rs
...   | inl rest = inl (all::_ wf rest)
...   | inr (bad-response r' r'∈tail ill') = inr (bad-response r' (there r'∈tail) ill')
```

### 6.2 Main endpoint dispatcher

```agda
WFEndpoint? : (e : Endpoint) → WFEndpoint e ∔ EndpointIllFormed e
WFEndpoint? e
  with WFPath? (Endpoint.route e) (Endpoint.parameters e)
... | inr illPath = inr (endpoint-path-ill-formed illPath)
... | inl wfPath
  with AllWFParams? (Endpoint.parameters e)
... | inr (bad-param p p∈ps illP) = inr (endpoint-parameter-ill-formed p p∈ps illP)
... | inl allWFParams
  with HasDuplicate? ParamKey≟ (paramKeys (Endpoint.parameters e))
... | inr dup = inr (endpoint-duplicate-parameters dup)
... | inl uniqParams
  with WFBody? (Endpoint.body e)
... | inr illBody = inr (endpoint-body-ill-formed illBody)
... | inl wfBody
  with AllWFResponses? (Endpoint.responses e)
... | inr (bad-response r r∈rs illR) = inr (endpoint-response-ill-formed r r∈rs illR)
... | inl allWFResps
  with HasDuplicate? Status≟ (respKeys (Endpoint.responses e))
... | inr dup = inr (endpoint-duplicate-statuses dup)
... | inl uniqResps =
      inl (wf-endpoint wfPath allWFParams uniqParams wfBody allWFResps uniqResps)
```

---


## 7. API Well-Formedness

`WFAPI?` is the top-level checker. It reuses `AllWFProps?` from section 1 for component schemas, `HasDuplicate? _≟_` for component name uniqueness,
`AllWFEndpoints?` for the path list, and `HasDuplicate? EndpointKey≟` for endpoint key uniqueness.

### 7.1 Endpoint list checker

```agda
EndpointKey≟ : (a b : Path × Method) → Dec (a ≡ b)
EndpointKey≟ (pa , ma) (pb , mb) with Path≟ pa pb
... | no  pa≢pb = no (λ { refl → pa≢pb refl })
... | yes refl
  with Method≟ ma mb
...   | no  ma≢mb = no (λ { refl → ma≢mb refl })
...   | yes refl  = yes refl

data BadEndpoint : List Endpoint → Set where
  bad-endpoint :
    ∀ {es}
    → (e : Endpoint)
    → e ∈ es
    → EndpointIllFormed e
    → BadEndpoint es

AllWFEndpoints? : (es : List Endpoint) → All WFEndpoint es ∔ BadEndpoint es
AllWFEndpoints? [] = inl all[]
AllWFEndpoints? (e :: es) with WFEndpoint? e
... | inr ill = inr (bad-endpoint e here ill)
... | inl wf
  with AllWFEndpoints? es
...   | inl rest = inl (all::_ wf rest)
...   | inr (bad-endpoint e' e'∈tail ill') = inr (bad-endpoint e' (there e'∈tail) ill')
```

### 7.2 Main API dispatcher

```agda
WFAPI? : (api : API) → WFAPI api ∔ APIIllFormed api
WFAPI? api
  with AllWFProps? (API.components api)
... | inr (bad-prop k s k,s∈comps illS) = inr (api-component-ill-formed k s k,s∈comps illS)
... | inl allWFComps
  with HasDuplicate? _≟_ (componentKeys api)
... | inr dup = inr (api-duplicate-components dup)
... | inl uniqComps
  with AllWFEndpoints? (API.paths api)
... | inr (bad-endpoint e e∈paths illE) = inr (api-endpoint-ill-formed e e∈paths illE)
... | inl allWFEndpoints
  with HasDuplicate? EndpointKey≟ (endpointKeys (API.paths api))
... | inr dup = inr (api-duplicate-endpoints dup)
... | inl uniqEndpoints =
      inl (wf-api allWFComps uniqComps allWFEndpoints uniqEndpoints)
```

`WFAPI?` is the entry point for the checker. Given any `API`, it either
produces a `WFAPI` proof that can be passed into semantic and refinement
definitions, or a structured `APIIllFormed` witness that can be walked to
explain exactly what went wrong, and where.