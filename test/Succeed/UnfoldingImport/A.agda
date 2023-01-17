{-# OPTIONS -vscope.top.opaque:60 #-}
module UnfoldingImport.A where


open import Agda.Builtin.Nat public

opaque
  x : Set
  x = Nat

  y : x
  y = 123
