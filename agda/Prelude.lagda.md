# Prelude

Minimal core definitions used across the project. Provides basic data types and simple logic without needing any external dependencies.

```agda
module Prelude where

postulate String : Set
{-# BUILTIN STRING String #-}
```

## Equality and basic logic

```agda
data _≡_ {A : Set} (x : A) : A → Set where
  refl : x ≡ x

data ⊤ : Set where
  tt : ⊤

data ⊥ : Set where

¬_ : Set → Set
¬ P = P → ⊥

_≢_ : ∀ {A : Set} → A → A → Set
x ≢ y = ¬ (x ≡ y)

data Dec (P : Set) : Set where
  yes : P → Dec P
  no  : (¬ P) → Dec P

postulate
  _≟_ : (x y : String) → Dec (x ≡ y)
```

## Basic data types

```agda
data Bool : Set where
  true false : Bool

if_then_else_ : ∀ {A : Set} → Bool → A → A → A
if true  then t else f = t
if false then t else f = f

data List (A : Set) : Set where
  []   : List A
  _::_  : A → List A → List A  

infixr 10 _::_

data Maybe (A : Set) : Set where
  nothing : Maybe A
  just    : A → Maybe A

just-inj : ∀ {A : Set} {x y : A} → just x ≡ just y → x ≡ y
just-inj refl = refl

record Σ (A : Set) (B : A → Set) : Set where
  constructor _,_
  field
    fst : A
    snd : B fst

_×_ : Set → Set → Set
A × B = Σ A (λ _ → B)

infixr 2 _×_

∃ : ∀ {A : Set} → (A → Set) → Set
∃ {A} P = Σ A P
```

## Equality Utilities

```agda
sym : ∀ {A : Set} {x y : A} → x ≡ y → y ≡ x
sym refl = refl

trans : ∀ {A : Set} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
trans refl q = q

cong : ∀ {A B : Set} {x y : A} → (f : A → B) → x ≡ y → f x ≡ f y
cong f refl = refl

subst : ∀ {A : Set} (P : A → Set) {x y : A} → x ≡ y → P x → P y
subst P refl px = px

⊥-elim : ∀ {A : Set} → ⊥ → A
⊥-elim ()
```

## List predicates / set-like reasoning on lists

```agda
data All {A : Set} (P : A → Set) : List A → Set where
  all[]  : All P []
  all::_ : ∀ {x xs} → P x → All P xs → All P (x :: xs)

infix 5 _∈_
data _∈_ {A : Set} : A → List A → Set where
  here  : ∀ {x xs} → x ∈ (x :: xs)
  there : ∀ {x y xs} → x ∈ xs → x ∈ (y :: xs)

data _∉_ {A : Set} (x : A) : List A → Set where
  notin[]  : x ∉ []
  notin::_ : ∀ {y ys} → x ≢ y → x ∉ ys → x ∉ (y :: ys)

∉-elim :
  ∀ {A : Set} {x : A} {xs : List A}
  → x ∉ xs
  → x ∈ xs
  → ⊥
∉-elim notin[] ()
∉-elim (notin::_ x≢y x∉ys) here        = x≢y refl
∉-elim (notin::_ _   x∉ys) (there x∈)  = ∉-elim x∉ys x∈

data Unique {A : Set} : List A → Set where
  uniq[]  : Unique []
  uniq::_ : ∀ {x xs} → x ∉ xs → Unique xs → Unique (x :: xs)

-- If every element of a list satisfies P, then any specific member satisfies P.
All-∈ :
  ∀ {A : Set} {P : A → Set} {x : A} {xs : List A}
  → All P xs
  → x ∈ xs
  → P x
All-∈ (all::_ px _)  here       = px
All-∈ (all::_ _ pxs) (there x∈)  = All-∈ pxs x∈

All-map :
    ∀ {A : Set} {P Q : A → Set} {xs : List A}
  → (∀ {a} → P a → Q a)
  → All P xs
  → All Q xs
All-map f all[] = all[]
All-map f (all::_ p ps) = all::_ (f p) (All-map f ps)

infix 4 _⊆_
_⊆_ : ∀ {A : Set} → List A → List A → Set
xs ⊆ ys = All (λ x → x ∈ ys) xs

⊆-refl : ∀ {A : Set} {xs : List A} → xs ⊆ xs
⊆-refl {xs = []} = all[]
⊆-refl {xs = x :: xs} =
  all::_ here (All-map there (⊆-refl {xs = xs}))

⊆-trans : ∀ {A : Set} {xs ys zs : List A} → xs ⊆ ys → ys ⊆ zs → xs ⊆ zs
⊆-trans xs⊆ys ys⊆zs =
  All-map (λ {x} x∈ys → All-∈ ys⊆zs x∈ys) xs⊆ys
```

## Association-list utils

```agda
keys : ∀ {A : Set} → List (String × A) → List String
keys [] = []
keys ((k , _) :: rest) = k :: keys rest

values : ∀ {A B : Set} → List (A × B) → List B
values [] = []
values ((_ , v) :: rest) = v :: values rest
```

## Preorder

```agda
record IsPreorder {A : Set} (_≤_ : A → A → Set) : Set where
  field
    reflexive  : ∀ {x} → _≤_ x x
    transitive : ∀ {x y z} → _≤_ x y → _≤_ y z → _≤_ x z
```
