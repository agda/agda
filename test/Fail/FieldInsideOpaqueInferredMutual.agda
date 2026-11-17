module FieldInsideOpaqueInferredMutual where

record R (A : Set) : Set where
  opaque
    identity : A → A
    field a : A
    identity x = x
