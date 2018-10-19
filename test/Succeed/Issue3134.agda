
open import Agda.Builtin.Nat
open import Agda.Builtin.Equality

postulate
  ⊤ ⊥ : Set
  _&_ : Set → Set → Set
  _≤_ : Nat → Nat → Set

{-# TERMINATING #-}
_∣_ : Nat → Nat → Set
m     ∣ zero  = ⊤
zero  ∣ suc n = ⊥
suc m ∣ suc n = (suc m ≤ suc n) & (suc m ∣ (n - m))

variable m n : Nat

postulate
  divide-to-nat : n ∣ m → Nat
  trivial : m ≡ n

divide-to-nat-correct : (e : m ∣ n) → divide-to-nat e * n ≡ m
divide-to-nat-correct e = trivial
