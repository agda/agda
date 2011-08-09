{-# OPTIONS --universe-polymorphism #-}

module Common.Equality where

open import Common.Level

infix 4 _≡_

data _≡_ {a} {A : Set a} (x : A) : A → Set a where
  refl : x ≡ x

{-# BUILTIN EQUALITY _≡_  #-}
{-# BUILTIN REFL     refl #-}
