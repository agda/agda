-- A1 needed for A2 but poisons B2

module A1 where

open import Base

postulate
  a≡true : a ≡ true

{-# REWRITE a≡true #-}
