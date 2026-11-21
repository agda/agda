module FieldInsideOpaqueNested where

record R (A : Set) : Set where
  opaque
    opaque
      field a : A
