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
HasDuplicate? : (xs : List String) → Unique xs ∔ HasDuplicate xs
HasDuplicate? [] = inl uniq[]
HasDuplicate? (x :: xs)
  with x ∈? xs
... | yes x∈xs = inr (dup-here x∈xs)
... | no  x∉xs
  with HasDuplicate? xs
...   | inr dup    = inr (dup-there dup)
...   | inl uniqXs = inl (uniq::_ (∉-intro x∉xs) uniqXs)
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
        with HasDuplicate? (keys (Schema.properties s))
  ...       | inr dupKeys = inr (object-duplicate-properties tyEq dupKeys)
  ...       | inl uniqKeys
          with HasDuplicate? (Schema.required s)
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
