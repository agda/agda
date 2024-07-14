-- Pattern-matching on refl is not size-decreasing
{-# OPTIONS --type-based-termination --no-syntax-based-termination #-}
module TypeBasedTermination.BadRefl where

open import Agda.Primitive

data Eq {ℓ : Level} {A : Set ℓ} (a : A) : A → Set (lsuc ℓ) where
  refl : Eq a a

p : ∀ {X Y : Set} → (Eq X Y) → X → Y
p refl x = p refl x
