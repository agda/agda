module OpaqueWhereData where

open import Agda.Builtin.Equality
open import Agda.Builtin.Nat

opaque
  foo : Nat
  foo = it where
    data Bar : Set where
    it : Nat
    it = 123
