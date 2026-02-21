# Compatibility

OpenAPI specs describe structural interaction constraints between clients and servers. These constraints form a contract, specifying which operations exist, which parameters must be supplied, and what shapes of responses are guaranteed.

Backwards compatibility therefore amounts to preservation of this contract under evolution. A new version of an API is compatible with an old one
precisely when it preserves all structural guarantees made by the old specification.

In our development, this notion is formalised using API refinement. Compatibility is defined as API refinement restricted to well-formed specifications.

```agda
module Semantics.Compatibility where

open import Prelude
open import Syntax.Syntax
open import WellFormed.Core

open import Semantics.APIRefinement
open import Semantics.APIRefinementProperties
```

---

## 1. Compatibility Definition

Compatibility is defined only for well-formed APIs. We reuse the type of well-formed APIs introduced in `APIRefinementProperties`.

```agda
_≈compat_ : WFAPIₛ → WFAPIₛ → Set
(a , _) ≈compat (b , _) = API⊑ a b
```

Intuitively, `(a , wfA) ≈compat (b , wfB)` means that `b` preserves all structural guarantees made by `a`, and is therefore a safe contract-preserving evolution.

---
