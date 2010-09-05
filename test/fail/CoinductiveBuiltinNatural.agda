module CoinductiveBuiltinNatural where

open import Imports.Coinduction

data ℕ : Set where
  zero : ℕ
  suc  : (n : ∞ ℕ) → ℕ

{-# BUILTIN NATURAL ℕ    #-}
{-# BUILTIN ZERO    zero #-}
{-# BUILTIN SUC     suc  #-}
