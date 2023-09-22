{-# OPTIONS --warning=error #-}
module OpaqueWhereOpaqueData where

open import Agda.Builtin.Equality
open import Agda.Builtin.Nat

opaque
  foo : Nat
  foo = it where
    data Bar : Set where
    opaque
      data Foo : Set where
    it : Nat
    it = 123
