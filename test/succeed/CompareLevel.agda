{-# OPTIONS --universe-polymorphism #-}
module CompareLevel where

open import Common.Level

postulate
  X : Set
  Foo : (a b : Level) → Set (a ⊔ b) → Set
  Bar : Foo _ _ X