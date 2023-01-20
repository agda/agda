{-# OPTIONS --hidden-argument-puns #-}

open import Agda.Builtin.Nat

private variable
  A : Set
  n : Nat

data Vec (A : Set) : Nat → Set where
  []  : Vec A zero
  _∷_ : A → Vec A n → Vec A (suc n)

pattern one = suc zero

-- The pun {one} is rejected, because one is a pattern synonym.

-- The error message should be pretty-printed correctly, using {one}
-- or {n = one} and {(A)} or {A = A}.

length : Set → ∀ {n A} → Vec A n → Nat
length = λ where
  _ {one} {(A)} _ → 1
  _ {n}         _ → n
