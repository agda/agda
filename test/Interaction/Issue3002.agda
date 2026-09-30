
open import Agda.Builtin.Equality
open import Agda.Builtin.Nat

data ⊥ : Set where

data Zero : Set where
  zero : Zero

data One : Set where
  suc : Zero → One

one : One
one = suc zero

data _≤_ : One → Zero → Set where

leq : ∀ m n → Nat → Nat → m ≤ n → ⊥
leq (suc m) zero = λ i j ()

test : Nat → one ≤ zero → ⊥
test = leq one zero 5

-- Normalise: test
-- Expected:  λ j ()
