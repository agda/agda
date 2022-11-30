{-# OPTIONS --polarity #-}

module _ where

data ⊤ : Set where
  tt : ⊤

f : @- Set → Set
f X = X → ⊤

data Wrong : Set where
  cons : f Wrong → Wrong
