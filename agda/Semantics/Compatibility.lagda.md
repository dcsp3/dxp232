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
(a₀ , wfₐ₀) ≈compat? (a₁ , wfₐ₁) = API⊑-decidable a₀ a₁ wfₐ₀ wfₐ₁
```

Therefore API evolution verification is decidable. Compatibility is not only well-defined but also algorithmically checkable.
