module FieldInsideOpaqueInstance where

record R (A : Set) : Set where
  opaque
    instance
      field a : A
