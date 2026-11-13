{-# OPTIONS --erasure #-}

module Issue434Erased where

record R (A : Set) : Set where
  field @0 a : A

  b : A
  b = a

  field c : A
