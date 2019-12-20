
open import Agda.Builtin.Nat
open import Agda.Builtin.Equality

-- Should not be accepted
f  : (@0 n : Nat) (m : Nat) → n + 0 ≡ m → Nat
f n m refl = m
