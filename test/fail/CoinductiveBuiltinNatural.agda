module CoinductiveBuiltinNatural where

open import Common.Coinduction

data ℕ : Set where
  zero : ℕ
  suc  : (n : ∞ ℕ) → ℕ

{-# BUILTIN NATURAL ℕ    #-}
