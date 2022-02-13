{-# OPTIONS --cubical #-}

module Erased-cubical-Module-application.Cubical (_ : Set₁) where

open import Agda.Builtin.Cubical.Path

data ∥_∥ (A : Set) : Set where
  ∣_∣     : A → ∥ A ∥
  trivial : (x y : ∥ A ∥) → x ≡ y
