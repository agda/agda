{-# OPTIONS --cubical #-}

module Issue6287-2.Cubical where

open import Agda.Builtin.Nat

record R : Set where
  constructor c
  field
    n : Nat
