module OpaqueUnfolding where

open import Agda.Builtin.Nat

opaque
  foo : Set₁
  foo = Set

opaque
  unfolding foo
  -- Unfolds bar
  bar : foo
  bar = Nat

opaque
  unfolding bar
  -- Unfolds foo and bar
  ty : Set
  ty = bar

  quux : ty
  quux = zero
