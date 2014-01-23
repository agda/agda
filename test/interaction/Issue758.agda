
data Nat : Set where
  zero : Nat
  suc  : Nat → Nat

pattern plus-two n = suc (suc n)

f : Nat → Nat
f (plus-two n) = f n
f (suc zero) = suc zero
f zero = zero
