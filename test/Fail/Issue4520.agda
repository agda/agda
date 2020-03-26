-- Andreas, 2020-03-18, issue #4520, reported by Dylan Ede.
--
-- Make the error message concerning ambiguous names
-- in BUILTIN declarations more precise.

open import Agda.Primitive
open import Agda.Builtin.FromNat
open import Agda.Builtin.Nat renaming (Nat to ℕ)

private
  variable
    ℓ ℓ' : Level

record FromNat (A : Set ℓ) : Set (lsuc ℓ) where
  field
    Constraint : ℕ → Set ℓ
    fromNat : (n : ℕ) ⦃ _ : Constraint n ⦄ → A
open FromNat ⦃ ... ⦄ public using (fromNat)

{-# BUILTIN FROMNAT fromNat #-}

-- ERROR WAS:
-- The argument to BUILTIN FROMNAT must be an unambiguous defined name
-- when scope checking the declaration
--   {-# BUILTIN FROMNAT fromNat #-}

-- NEW ERROR:
-- Name  fromNat  is ambiguous
-- when scope checking the declaration
--   {-# BUILTIN FROMNAT fromNat #-}
