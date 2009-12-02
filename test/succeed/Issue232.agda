{-# OPTIONS --universe-polymorphism #-}

module Issue232 where

open import Common.Level

data T {ℓ} : {α : Set ℓ} → α → Set (suc ℓ) where
  c : {α : Set ℓ} {x : α} → T x
