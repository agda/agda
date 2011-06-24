{-# OPTIONS --universe-polymorphism #-}

module SetOmega where

open import Imports.Level

postulate
  IsType : ∀ {a} → Set a → Set
  Bad : IsType ((a : Level) → Set a)
