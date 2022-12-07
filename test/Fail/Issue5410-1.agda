{-# OPTIONS --erasure #-}

module _ where

open import Agda.Builtin.Bool

module M (b : Bool) where

  some-boolean : Bool
  some-boolean = b

@0 A : @0 Bool → Set
A b = Bool
  module A where
    module M′ = M b

bad : @0 Bool → Bool
bad = A.M′.some-boolean
