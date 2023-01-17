module OpaqueSibling where

open import Agda.Builtin.Equality
open import Agda.Builtin.Nat

opaque
  foo : Nat
  foo = 1

  bar : Nat
  bar = 2

opaque unfolding (foo) where
  _ : bar ≡ 2
  _ = refl
