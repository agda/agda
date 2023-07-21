{-# OPTIONS --warning=error -WnoUselessOpaque #-}
module OpaqueUnfoldTransparent where

open import Agda.Builtin.Nat

foo : Nat
foo = 123

opaque
  unfolding foo
