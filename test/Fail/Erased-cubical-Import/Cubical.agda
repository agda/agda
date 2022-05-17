{-# OPTIONS --cubical #-}

module Erased-cubical-Import.Cubical where

open import Agda.Builtin.Cubical.Path

data ∥_∥ (A : Set) : Set where
  ∣_∣     : A → ∥ A ∥
  trivial : (x y : ∥ A ∥) → x ≡ y
