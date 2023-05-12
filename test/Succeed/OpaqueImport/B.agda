{-# OPTIONS -vscope.opaque:667 #-}
module OpaqueImport.B where

open import Agda.Builtin.Equality
open import OpaqueImport.A

opaque
  unfolding y
  z : x
  z = 123

  _ : z ≡ y
  _ = refl
