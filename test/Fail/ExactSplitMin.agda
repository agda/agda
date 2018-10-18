{-# OPTIONS --exact-split -Werror #-}

module ExactSplitMin where

data ℕ : Set where
  zero : ℕ
  suc  : ℕ → ℕ

min : ℕ → ℕ → ℕ
min zero    y       = zero
min x       zero    = zero
min (suc x) (suc y) = suc (min x y)
