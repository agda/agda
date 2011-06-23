------------------------------------------------------------------------
-- Universes
------------------------------------------------------------------------

{-# OPTIONS --universe-polymorphism #-}

module Universe where

open import Level

-- Universes.

record Universe u e : Set (suc (u ⊔ e)) where
  field
    -- Codes.
    U : Set u

    -- Decoding function.
    El : U → Set e
