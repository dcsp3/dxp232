# Prelude

Minimal core definitions used across the project. Provides basic data types and simple logic without needing any external dependencies.

```agda
module Prelude where

postulate String : Set

{-# BUILTIN STRING String #-}

data List (A : Set) : Set where
  []   : List A
  _::_  : A → List A → List A  

infixr 10 _::_

data _×_ (A B : Set) : Set where
  _,_ : A → B → A × B

data Maybe (A : Set) : Set where
  nothing : Maybe A
  just    : A → Maybe A

data _≡_ {A : Set} (x : A) : A → Set where
  refl : x ≡ x

data ⊥ : Set where

¬_ : Set → Set
¬ P = P → ⊥

_≢_ : ∀ {A : Set} → A → A → Set
x ≢ y = ¬ (x ≡ y)
```
