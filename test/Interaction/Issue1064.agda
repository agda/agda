{-# OPTIONS --guardedness #-}

data D : Set where

record R : Set where
  constructor d
  field x : D

record R′ : Set where
  coinductive
  constructor d
  field r : R′

f : R → D
f r = let d x = r in x
