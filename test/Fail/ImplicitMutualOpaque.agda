module ImplicitMutualOpaque where

open import Agda.Builtin.Nat

test : Nat
opaque
  foo : Nat
  foo = test
test = 2
