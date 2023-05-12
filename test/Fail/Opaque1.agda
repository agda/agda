module Opaque1 where

open import Agda.Builtin.Nat

opaque
  foo : Set₁
  foo = Set

opaque
  bar : foo
  bar = Nat
