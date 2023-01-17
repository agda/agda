module Fail.Opaque1 where

open import Agda.Builtin.Nat

opaque
  foo : Set₁
  foo = Set

opaque unfolding () where
  bar : foo
  bar = Nat
