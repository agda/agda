open import Agda.Builtin.Nat

f : Nat
f with zero
... | n with (suc n)
... | m = m
