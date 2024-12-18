{-# OPTIONS --polarity #-}

module _ where

data ⊤ : Set where
  tt : ⊤

data Wrong (@++ A : Set) : Set where
  cons : (A → ⊤) → Wrong A
