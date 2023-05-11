{-# OPTIONS --hidden-argument-puns #-}

open import Agda.Builtin.Nat

private variable
  A : Set
  n : Nat

data Vec (A : Set) : Nat → Set where
  []  : Vec A zero
  _∷_ : A → Vec A n → Vec A (suc n)

-- The pun ⦃ zero ⦄ is rejected, because zero is a constructor.

-- The error message should be pretty-printed correctly, using
-- ⦃ zero ⦄ or ⦃ n = zero ⦄ and {(A)} or {A = A}.

length : ∀ ⦃ n ⦄ {A} → Vec A n → Nat
length ⦃ zero ⦄  {(A)} _ = zero
length ⦃ suc n ⦄       _ = suc n
