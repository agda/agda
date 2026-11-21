module FieldInsideOpaquePrivate where

record R (A : Set) : Set where
  opaque
    private
      field a : A
