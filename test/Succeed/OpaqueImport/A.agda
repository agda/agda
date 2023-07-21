{-# OPTIONS -vscope.opaque:667 #-}
module OpaqueImport.A where

open import Agda.Builtin.Nat public

opaque
  x : Set
  x = Nat

  y : x
  y = 123
