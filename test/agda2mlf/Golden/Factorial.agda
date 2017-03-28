module Golden.Factorial where

open import Agda.Builtin.Nat

fac : Nat -> Nat
fac 0 = 1
fac (suc n) = suc n * fac n

a = fac 0
b = fac 10
