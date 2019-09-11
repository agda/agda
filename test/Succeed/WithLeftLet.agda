module WithLeftLet where

open import Agda.Builtin.Nat
open import Agda.Builtin.Equality

f : (n : Nat) -> Nat
f n using 2n <- n + n | 3n <- 2n + n | 4n <- 3n + n = 2n

f' : (n : Nat) -> Nat
f' n using 2n <- n + n | 3n <- 2n + n | 4n <- 3n + n with 5n <- 4n + n = 5n
