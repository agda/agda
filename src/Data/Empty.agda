------------------------------------------------------------------------
-- Empty type
------------------------------------------------------------------------

{-# OPTIONS --universe-polymorphism #-}

module Data.Empty where

open import Level

data ⊥ : Set where

{-# IMPORT Data.FFI #-}
{-# COMPILED_DATA ⊥ Data.FFI.AgdaEmpty #-}

⊥-elim : ∀ {w} {Whatever : Set w} → ⊥ → Whatever
⊥-elim ()
