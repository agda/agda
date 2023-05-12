module Opaque2 where

open import Agda.Builtin.Nat

opaque
  foo : Set₁
  foo = Set

opaque
  unfolding foo
  bar : foo
  bar = Nat

opaque
  unfolding foo
  ty : Set
  ty = bar

  baz : ty
  baz = 123
