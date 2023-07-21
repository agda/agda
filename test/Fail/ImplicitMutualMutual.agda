module ImplicitMutualMutual where

open import Agda.Builtin.Nat

test : Nat
mutual
  foo : Nat
  foo = test
test = 2
