open import Agda.Primitive
open import Agda.Builtin.Nat
open import Agda.Builtin.Equality

variable
  a : Level
  A : Set a
  n : Nat

idNat : Nat → Nat
idNat zero = zero
idNat (suc n) = suc n

postulate
  Vec : (a : Level) (A : Set a) → Nat → Set a
  f   : (n : Nat) → Vec _ A (idNat n)
  P   : (a : Level) (A : Set a) (n : Nat) → Vec _ A n → Set

-- Jesper, 2025-05-13: Looking into the solution of BlockedConst in
-- the implementation of constraintMetas causes the generalization to
-- fail here.
postulate
  _ : (a : A) → P _ A (idNat n) (f _)
