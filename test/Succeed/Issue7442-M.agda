
{-# OPTIONS --erasure --cubical #-}

data ⊥ : Set where

record R : Set where
  field
    f : ⊥
