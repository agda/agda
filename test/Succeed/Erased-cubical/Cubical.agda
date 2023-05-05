{-# OPTIONS --safe --cubical --erasure #-}

module Erased-cubical.Cubical where

open import Agda.Builtin.Cubical.Path

data ∥_∥ (A : Set) : Set where
  ∣_∣     : A → ∥ A ∥
  trivial : (x y : ∥ A ∥) → x ≡ y

data D′ : Set where
  @0 c′ : D′
