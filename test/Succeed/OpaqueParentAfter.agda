module OpaqueParentAfter where

open import Agda.Builtin.Nat
open import Agda.Builtin.Equality

opaque
  x : Nat
  x = 1

  opaque
    y : Nat
    y = 2

  z : Nat
  z = 3

opaque
  unfolding y
  _ : z ≡ 3
  _ = refl
