{-# OPTIONS --erasure #-}

-- Andreas, 2018-10-16, runtime erasure
--
-- Should not be able to extract erased constructor field.

open import Agda.Builtin.Nat

data Vec (A : Set) : Nat → Set where
  [] : Vec A zero
  _∷_ : {@0 n : Nat} (x : A) (xs : Vec A n) → Vec A (suc n)

length : ∀{A} {@0 n} (x : Vec A n) → Nat
length [] = zero
length (_∷_ {n} _ _) = suc n

-- Expected error:
--
-- Variable n is declared erased, so it cannot be used here
-- when checking that the expression n has type Nat
