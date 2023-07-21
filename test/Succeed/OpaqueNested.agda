module OpaqueNested where

open import Agda.Builtin.Nat
open import Agda.Builtin.Equality

opaque
  foo : Nat
  foo = 2

opaque
  bar : Nat
  bar = 2

module C where
  -- No warning should be printed:
  opaque
    unfolding bar
    opaque
      unfolding foo

      _ : foo + bar ≡ 4
      _ = refl
