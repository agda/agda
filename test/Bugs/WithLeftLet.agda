module WithLeftLet where

open import Agda.Builtin.Nat
open import Agda.Builtin.Equality

f : (n : Nat) -> Nat
f n using 2n <- n + n with 3n <- 2n + n using 4n <- 3n + n = 2n
