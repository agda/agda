-- Andreas, 2024-09-04
-- Ensure that type emptiness check works with guarded records
-- Re: https://github.com/agda/agda/issues/7467#issuecomment-2327177373

open import Agda.Builtin.Maybe

data ⊥ : Set where

record NEList (A : Set) : Set where
  inductive
  field
    hd : A
    tl : Maybe (NEList A)

f : NEList ⊥ → ⊥
f ()

-- Should succeed.
