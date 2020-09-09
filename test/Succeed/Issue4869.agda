module Issue4869 where

open import Agda.Builtin.Nat

infix 4 _≤_

data _≤_ : Nat → Nat → Set where
  z≤n : ∀ {n} → zero ≤ n
  s≤s : ∀ {m n} (m≤n : m ≤ n) → suc m ≤ suc n

foo : 2 ≤ 1 → Nat
foo (s≤s ()) = 123
