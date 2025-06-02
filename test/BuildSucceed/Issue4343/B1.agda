-- B1 needed for B2 but poisons A2

module B1 where

open import Base

postulate
  b≡true : b ≡ false

{-# REWRITE b≡true #-}
