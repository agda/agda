module OpaqueParent where

open import Agda.Builtin.Nat
open import Agda.Builtin.Equality

opaque
  x : Nat
  x = 1

  opaque
    y : Nat
    y = 2

opaque
  unfolding y
  _ : x ≡ 1
  _ = refl
