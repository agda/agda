module OpaqueSibling where

open import Agda.Builtin.Equality
open import Agda.Builtin.Nat

opaque
  f : Nat
  f = 1
  opaque
    g : Nat
    g = 2
  opaque
    h : Nat
    h = 3

opaque
  unfolding g

  k : Nat
  k = (f + g) + h

  shouldFail : k ≡ 6
  shouldFail = refl
