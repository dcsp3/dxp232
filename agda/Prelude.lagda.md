# Prelude

Minimal core definitions used across the project. Provides basic data types and simple logic without needing any external dependencies.

```agda
module Prelude where

postulate String : Set
{-# BUILTIN STRING String #-}
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

data _×_ (A B : Set) : Set where
  _,_ : A → B → A × B

fst : ∀ {A B : Set} → A × B → A
fst (a , b) = a

snd : ∀ {A B : Set} → A × B → B
snd (a , b) = b

data Maybe (A : Set) : Set where
  nothing : Maybe A
  just    : A → Maybe A
```

## Equality and basic logic

```agda
data _≡_ {A : Set} (x : A) : A → Set where
  refl : x ≡ x

data ⊥ : Set where

¬_ : Set → Set
¬ P = P → ⊥

_≢_ : ∀ {A : Set} → A → A → Set
x ≢ y = ¬ (x ≡ y)
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

infix 4 _⊆_
_⊆_ : ∀ {A : Set} → List A → List A → Set
xs ⊆ ys = All (λ x → x ∈ ys) xs
```

## Association-list utils (DSL-agnostic)

```agda
keys : ∀ {A : Set} → List (String × A) → List String
keys [] = []
keys (kv :: rest) = fst kv :: keys rest
```
