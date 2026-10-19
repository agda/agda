-- Andreas, 2025-10-25, reproduce error CannotGeneralizeEtaExpandable

record ⊤ : Set where

variable
  x : ⊤
  P : ⊤ → Set

postulate
  cant-generalize : P x

-- Expected error: [CannotGeneralizeEtaExpandable]
-- Cannot generalize over x of eta-expandable type ⊤
-- when checking that the expression P x is a type
