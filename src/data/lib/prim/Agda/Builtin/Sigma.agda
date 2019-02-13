{-# OPTIONS --without-K --safe --no-sized-types --no-guardedness #-}

module Agda.Builtin.Sigma where

open import Agda.Primitive

record Σ {a b} (A : Set a) (B : A → Set b) : Set (a ⊔ b) where
  constructor _,_
  field
    fst : A
    snd : B fst

open Σ public

infixr 4 _,_

{-# BUILTIN SIGMA Σ #-}
