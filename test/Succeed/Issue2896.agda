open import Agda.Builtin.Nat

data D : Nat → Set where
  c : (n : Nat) → D n

foo : (m : Nat) → D (suc m) → Nat
foo m (c (suc n)) = m + n
