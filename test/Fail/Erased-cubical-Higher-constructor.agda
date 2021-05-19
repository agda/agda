{-# OPTIONS --erased-cubical #-}

open import Agda.Builtin.Cubical.Path

-- Higher constructors must be erased when --erased-cubical is used.

data ∥_∥ (A : Set) : Set where
  ∣_∣     : A → ∥ A ∥
  trivial : (x y : ∥ A ∥) → x ≡ y
