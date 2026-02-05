# Variance

“Safe evolution” of APIs depends on *who is observing the change*:

- **Covariant** positions (`Co`): values are **consumed by the client** (e.g. responses).  
  A change is safe if the new schema is a safe replacement for what clients previously consumed.

- **Contravariant** positions (`Contra`): values are **consumed by the server** (e.g. requests).  
  A change is safe if the new server accepts at least what the old server accepted.

We implement contravariance uniformly via a simple `flip` operation, so refinement rules only need to be written once (for the covariant case) and reused everywhere.

---

```agda
module Semantics.Variance where

data Variance : Set where
  Co     : Variance   -- client-observed positions (e.g. responses)
  Contra : Variance   -- server-observed positions (e.g. requests)

flip : Variance → Variance
flip Co     = Contra
flip Contra = Co
```
