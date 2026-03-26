# Compatibility

This module packages API refinement as a notion of backward compatibility for well-formed OpenAPI specifications.

A new API version is compatible with an old one precisely when it refines it.

```agda
module Semantics.Compatibility where

open import Prelude
open import Syntax.Syntax
open import WellFormed.Core

open import Semantics.APIRefinement
open import Semantics.APIRefinementProperties
open import Semantics.DecidableRefinement
open import Semantics.DriftProperties
```

---

## 1. Compatibility Definition

Compatibility is API refinement restricted to well-formed APIs.

```agda
_≈compat_ : WFAPIₛ → WFAPIₛ → Set
(a , _) ≈compat (b , _) = API⊑ a b
```

Thus, `(a , wfA) ≈compat (b , wfB)` means that `b` refines `a`.

---

## 2. Decidable Compatibility

Compatibility is decidable for well-formed APIs.

```agda
_≈compat?_ : (a₀ a₁ : WFAPIₛ) → Dec (a₀ ≈compat a₁)
(a₀ , wfₐ₀) ≈compat? (a₁ , wfₐ₁)
  with API⊑? a₀ a₁ wfₐ₀ wfₐ₁
... | inl ok    = yes ok
... | inr drift = no (DriftSound drift)
```

The procedure either returns a proof of compatibility or a structural witness of incompatibility.

---

## 3. API Equivalence

Two APIs are equivalent when compatibility holds in both directions.

```agda
_≈equiv_ : WFAPIₛ → WFAPIₛ → Set
a ≈equiv b = (a ≈compat b) × (b ≈compat a)
```

This is also decidable by checking both directions independently.

```agda
_≈equiv?_ : (a₀ a₁ : WFAPIₛ) → Dec (a₀ ≈equiv a₁)
a₀ ≈equiv? a₁ = (a₀ ≈compat? a₁) ×-dec (a₁ ≈compat? a₀)
```
