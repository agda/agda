{-# OPTIONS --without-K --erasure #-}

data D : Set where
  @0 c : D

data P (x : D) : Set where

record R : Set where
  field
    f : P c
