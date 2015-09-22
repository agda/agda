module NaturalAndLevelDifferent where

data ℕ : Set where
  zero : ℕ
  suc  : ℕ → ℕ

{-# BUILTIN NATURAL ℕ #-}
{-# BUILTIN LEVEL   ℕ #-}
