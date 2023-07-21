{-# OPTIONS -vscope.opaque:667 #-}
module OpaqueImport.C where

open import Agda.Builtin.Equality
open import OpaqueImport.A
open import OpaqueImport.B

opaque
  unfolding z

  _ : x ≡ Nat
  _ = refl
