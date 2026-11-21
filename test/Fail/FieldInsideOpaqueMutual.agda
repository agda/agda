module FieldInsideOpaqueMutual where

record R (A : Set) : Set where
  opaque
    mutual
      field a : A
