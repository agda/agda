module ImplicitMutualInterleavedMutual where

open import Agda.Builtin.Nat

test : Nat
interleaved mutual
  foo : Nat
  foo = test
test = 2
