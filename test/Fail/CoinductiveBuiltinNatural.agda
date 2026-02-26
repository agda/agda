{-# OPTIONS --guardedness #-}

module CoinductiveBuiltinNatural where

open import Agda.Builtin.Coinduction

data ℕ : Set where
  zero : ℕ
  suc  : (n : ∞ ℕ) → ℕ

{-# BUILTIN NATURAL ℕ    #-}
