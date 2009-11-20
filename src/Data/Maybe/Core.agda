{-# OPTIONS --universe-polymorphism #-}
------------------------------------------------------------------------
-- The Maybe type
------------------------------------------------------------------------

-- The definitions in this file are reexported by Data.Maybe.

module Data.Maybe.Core where

open import Level

data Maybe {ℓ} (A : Set ℓ) : Set ℓ where
  just    : (x : A) → Maybe A
  nothing : Maybe A
