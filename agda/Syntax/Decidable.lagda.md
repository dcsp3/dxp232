# Decidable Equality for Syntax

Many refinement relations in the semantic layer rely on aligning syntactic
objects via lookup. This requires decidable equality on key syntactic types
such as `Method`, `Status`, and `Path`.

This module collects those equality procedures in one place. It provides the
computational infrastructure needed by refinement definitions, while keeping
semantic modules focused solely on reasoning rather than comparison.

```agda
module Syntax.Decidable where

open import Prelude
open import Syntax.Syntax
```

## 1. List equality

```agda
List≟ :
  ∀ {A}
  → (∀ x y → Dec (x ≡ y))
  → (xs ys : List A)
  → Dec (xs ≡ ys)

List≟ eq [] [] = yes refl
List≟ eq [] (_ :: _) = no (λ ())
List≟ eq (_ :: _) [] = no (λ ())

List≟ eq (x :: xs) (y :: ys)
  with eq x y
... | no neq =
      no (λ { refl → neq refl })

... | yes refl
  with List≟ eq xs ys
...   | yes refl = yes refl
...   | no neq =
        no (λ { refl → neq refl })
```

---

## 2. Base equality

```agda
Base≟ : (a b : Base) → Dec (a ≡ b)
Base≟ integer integer = yes refl
Base≟ string  string  = yes refl
Base≟ boolean boolean = yes refl
Base≟ number  number  = yes refl
Base≟ object  object  = yes refl
Base≟ array   array   = yes refl

Base≟ integer string  = no (λ ())
Base≟ integer boolean = no (λ ())
Base≟ integer number  = no (λ ())
Base≟ integer object  = no (λ ())
Base≟ integer array   = no (λ ())

Base≟ string  integer = no (λ ())
Base≟ string  boolean = no (λ ())
Base≟ string  number  = no (λ ())
Base≟ string  object  = no (λ ())
Base≟ string  array   = no (λ ())

Base≟ boolean integer = no (λ ())
Base≟ boolean string  = no (λ ())
Base≟ boolean number  = no (λ ())
Base≟ boolean object  = no (λ ())
Base≟ boolean array   = no (λ ())

Base≟ number  integer = no (λ ())
Base≟ number  string  = no (λ ())
Base≟ number  boolean = no (λ ())
Base≟ number  object  = no (λ ())
Base≟ number  array   = no (λ ())

Base≟ object  integer = no (λ ())
Base≟ object  string  = no (λ ())
Base≟ object  boolean = no (λ ())
Base≟ object  number  = no (λ ())
Base≟ object  array   = no (λ ())

Base≟ array   integer = no (λ ())
Base≟ array   string  = no (λ ())
Base≟ array   boolean = no (λ ())
Base≟ array   number  = no (λ ())
Base≟ array   object  = no (λ ())
```

---

## 2.1 Primitive base classifier

```agda
IsPrimitive? : (b : Base) → Dec (IsPrimitive b)
IsPrimitive? integer = yes prim-integer
IsPrimitive? string  = yes prim-string
IsPrimitive? boolean = yes prim-boolean
IsPrimitive? number  = yes prim-number
IsPrimitive? object  = no (λ ())
IsPrimitive? array   = no (λ ())
```

---

## 3. Method equality

```agda
Method≟ : (a b : Method) → Dec (a ≡ b)
Method≟ GET    GET    = yes refl
Method≟ POST   POST   = yes refl
Method≟ PUT    PUT    = yes refl
Method≟ DELETE DELETE = yes refl
Method≟ PATCH  PATCH  = yes refl

Method≟ GET    POST   = no (λ ())
Method≟ GET    PUT    = no (λ ())
Method≟ GET    DELETE = no (λ ())
Method≟ GET    PATCH  = no (λ ())

Method≟ POST   GET    = no (λ ())
Method≟ POST   PUT    = no (λ ())
Method≟ POST   DELETE = no (λ ())
Method≟ POST   PATCH  = no (λ ())

Method≟ PUT    GET    = no (λ ())
Method≟ PUT    POST   = no (λ ())
Method≟ PUT    DELETE = no (λ ())
Method≟ PUT    PATCH  = no (λ ())

Method≟ DELETE GET    = no (λ ())
Method≟ DELETE POST   = no (λ ())
Method≟ DELETE PUT    = no (λ ())
Method≟ DELETE PATCH  = no (λ ())

Method≟ PATCH  GET    = no (λ ())
Method≟ PATCH  POST   = no (λ ())
Method≟ PATCH  PUT    = no (λ ())
Method≟ PATCH  DELETE = no (λ ())
```

---

## 4. Status equality

```agda
Status≟ : (a b : Status) → Dec (a ≡ b)
Status≟ OK         OK         = yes refl
Status≟ NotFound   NotFound   = yes refl
Status≟ BadRequest BadRequest = yes refl
Status≟ NoContent  NoContent  = yes refl

Status≟ OK         NotFound   = no (λ ())
Status≟ OK         BadRequest = no (λ ())
Status≟ OK         NoContent  = no (λ ())

Status≟ NotFound   OK         = no (λ ())
Status≟ NotFound   BadRequest = no (λ ())
Status≟ NotFound   NoContent  = no (λ ())

Status≟ BadRequest OK         = no (λ ())
Status≟ BadRequest NotFound   = no (λ ())
Status≟ BadRequest NoContent  = no (λ ())

Status≟ NoContent  OK         = no (λ ())
Status≟ NoContent  NotFound   = no (λ ())
Status≟ NoContent  BadRequest = no (λ ())

Status≟-refl : ∀ {st} → Status≟ st st ≡ yes refl
Status≟-refl {OK}         = refl
Status≟-refl {NotFound}   = refl
Status≟-refl {BadRequest} = refl
Status≟-refl {NoContent}  = refl
```

---

## 5. ParamLocation equality

```agda
ParamLocation≟ : (a b : ParamLocation) → Dec (a ≡ b)
ParamLocation≟ path  path  = yes refl
ParamLocation≟ query query = yes refl
ParamLocation≟ path  query = no (λ ())
ParamLocation≟ query path  = no (λ ())
```

---

## 6. ParamKey equality

```agda
ParamKey≟ : (a b : ParamLocation × String) → Dec (a ≡ b)
ParamKey≟ (la , na) (lb , nb) with ParamLocation≟ la lb
... | no  la≢lb = no (λ { refl → la≢lb refl })
... | yes refl  with na ≟ nb
...   | no  na≢nb = no (λ { refl → na≢nb refl })
...   | yes refl  = yes refl
```

---

## 7. PathSegment equality

```agda
PathSegment≟ : (a b : PathSegment) → Dec (a ≡ b)

PathSegment≟ (lit s₁) (lit s₂)
  with s₁ ≟ s₂
... | yes refl = yes refl
... | no neq   = no (λ { refl → neq refl })

PathSegment≟ (param s₁) (param s₂)
  with s₁ ≟ s₂
... | yes refl = yes refl
... | no neq   = no (λ { refl → neq refl })

PathSegment≟ (lit _) (param _) = no (λ ())
PathSegment≟ (param _) (lit _) = no (λ ())
```

---

## 8. Path equality

```agda
Path≟ : (p q : Path) → Dec (p ≡ q)
Path≟ p q
  with List≟ PathSegment≟ (Path.segments p) (Path.segments q)
... | yes refl = yes refl
... | no neq   = no (λ { refl → neq refl })
```
