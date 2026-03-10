# Compatibility

OpenAPI specifications encode structural contracts: which operations exist, which parameters are required, and which response shapes are guaranteed.

Backward compatibility captures preservation of this contract under evolution. A new API version is compatible with an old one when it preserves the structural guarantees provided by the old specification.

In this development, compatibility is formalised as API refinement restricted to well-formed specifications. This restriction is important because it supports deterministic lookup and, consequently, decidable checking.

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

Compatibility restricts API refinement to well-formed specifications. Well-formedness (unique keys, proper nesting) makes decidability possible by guaranteeing deterministic lookup.

```agda
_≈compat_ : WFAPIₛ → WFAPIₛ → Set
(a , _) ≈compat (b , _) = API⊑ a b
```

Thus, `(a , wfA) ≈compat (b , wfB)` means that `b` refines `a`: every component and endpoint in `a` is preserved in `b` with a compatible type change. This is the formal notion of contract preservation.

---

## 2. Decidable Compatibility

Backward compatibility is decidable for well-formed APIs. Given two well-formed OpenAPI specifications, we can either construct a compatibility proof or return a structural witness of incompatibility.

```agda
_≈compat?_ : (a₀ a₁ : WFAPIₛ) → Dec (a₀ ≈compat a₁)
(a₀ , wfₐ₀) ≈compat? (a₁ , wfₐ₁)
  with API⊑? a₀ a₁ wfₐ₀ wfₐ₁
... | inl ok    = yes ok
... | inr drift = no (DriftSound drift)
```

Therefore API evolution verification is decidable. Compatibility is not only well-defined but also algorithmically checkable.

---

## 3. API Equivalence

Two APIs are equivalent when compatibility holds in both directions. This is useful for bidirectional compatibility analysis and for checking whether refactorings preserve observable behaviour.

```agda
_≈equiv_ : WFAPIₛ → WFAPIₛ → Set
a ≈equiv b = (a ≈compat b) × (b ≈compat a)
```

Equivalence is also decidable by checking both compatibility directions independently.

```agda
_≈equiv?_ : (a₀ a₁ : WFAPIₛ) → Dec (a₀ ≈equiv a₁)
a₀ ≈equiv? a₁ = (a₀ ≈compat? a₁) ×-dec (a₁ ≈compat? a₀)
```
