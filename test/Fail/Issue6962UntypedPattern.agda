module Issue6962UntypedPattern where

open import Agda.Builtin.Nat

f (n : Nat) (suc m) : Nat
f = n
