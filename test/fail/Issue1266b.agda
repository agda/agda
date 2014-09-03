-- Andreas, 2014-09-02

module _ where

module Data where
  data D : Set where
    A : D

module _ (A : Set) where

  open Data using (D; A)

  x : D
  x = A

