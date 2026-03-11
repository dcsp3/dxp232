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

{-# BUILTIN EQUALITY _≡_ #-}

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
```

## Basic data types

```agda
data Bool : Set where
  true false : Bool

{-# BUILTIN BOOL  Bool  #-}
{-# BUILTIN TRUE  true  #-}
{-# BUILTIN FALSE false #-}

private
  primitive
    primStringEquality : String → String → Bool

_≟_ : (x y : String) → Dec (x ≡ y)
_≟_ x y with primStringEquality x y
... | true  = yes primTrustMe
  where postulate primTrustMe : x ≡ y
... | false = no primTrustMe
  where postulate primTrustMe : x ≢ y
  
true≢false : true ≡ false → ⊥
true≢false ()

false≢true : false ≡ true → ⊥
false≢true ()

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

just≢nothing : ∀ {A} {x : A} → just x ≢ nothing
just≢nothing ()

record Σ (A : Set) (B : A → Set) : Set where
  constructor _,_
  field
    fst : A
    snd : B fst

_×_ : Set → Set → Set
A × B = Σ A (λ _ → B)

infixr 2 _×_

_×-dec_ : ∀ {P Q : Set} → Dec P → Dec Q → Dec (P × Q)
yes p ×-dec yes q = yes (p , q)
yes p ×-dec no ¬q = no (λ where (_ , q) → ¬q q)
no ¬p ×-dec _ = no (λ where (p , _) → ¬p p)

∃ : ∀ {A : Set} → (A → Set) → Set
∃ {A} P = Σ A P

infixr 4 _∔_

data _∔_ (A B : Set) : Set where
  inl : A → A ∔ B
  inr : B → A ∔ B
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

pair-≡ :
    ∀ {A B : Set} {a a' : A} {b b' : B}
  → a ≡ a'
  → b ≡ b'
  → (a , b) ≡ (a' , b')
pair-≡ refl refl = refl

≢-transport :
    ∀ {A : Set} {x y z : A}
  → x ≢ y
  → y ≡ z
  → x ≢ z
≢-transport x≢y y≡z x≡z =
  x≢y (trans x≡z (sym y≡z))

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

∈-empty : ∀ {A} {x : A} → x ∈ [] → ⊥
∈-empty ()

data _∉_ {A : Set} (x : A) : List A → Set where
  notin[]  : x ∉ []
  notin::_ : ∀ {y ys} → x ≢ y → x ∉ ys → x ∉ (y :: ys)

∉-intro : ∀ {x : String} {xs : List String} → ¬ (x ∈ xs) → x ∉ xs
∉-intro {xs = []} _ = notin[]
∉-intro {x} {xs = y :: ys} ¬∈
  with x ≟ y
... | yes refl = ⊥-elim (¬∈ here)
... | no  x≢y  = notin::_ x≢y (∉-intro (λ x∈ys → ¬∈ (there x∈ys)))

∉-intro-gen : ∀ {A} {x : A} {xs : List A} → ((a b : A) → Dec (a ≡ b)) → ¬ (x ∈ xs) → x ∉ xs
∉-intro-gen {xs = []} _ _ = notin[]
∉-intro-gen {x = x} {xs = y :: ys} eq ¬∈
  with eq x y
... | yes refl = ⊥-elim (¬∈ here)
... | no  x≢y  = notin::_ x≢y (∉-intro-gen eq (λ x∈ys → ¬∈ (there x∈ys)))

∉-elim : ∀ {A : Set} {x : A} {xs : List A} → x ∉ xs → x ∈ xs → ⊥
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

∈?-gen : ∀ {A} → ((x y : A) → Dec (x ≡ y)) → (x : A) → (xs : List A) → Dec (x ∈ xs)
∈?-gen eq x [] = no (λ ())
∈?-gen eq x (y :: ys) with eq x y
... | yes refl = yes here
... | no  x≢y  with ∈?-gen eq x ys
...   | yes p  = yes (there p)
...   | no ¬p  = no (λ { here → x≢y refl ; (there q) → ¬p q })

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

⊆-counterexample : ∀ {xs ys} → ¬ (xs ⊆ ys) → Σ String (λ k → k ∈ xs × k ∉ ys)
⊆-counterexample {[]} ¬sub = ⊥-elim (¬sub all[])
⊆-counterexample {x :: xs} {ys} ¬sub
  with x ∈? ys
... | no  x∉ys = x , (here , ∉-intro x∉ys)
... | yes x∈ys
  with ⊆-counterexample (λ rest → ¬sub (all::_ x∈ys rest))
... | (k , (k∈ , k∉)) = k , (there k∈ , k∉)
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
