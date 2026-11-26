-- Reject this before record staging, which used to crash on the hidden field.
module Issue434OpaqueField where

record R (A : Set) : Set where
  opaque
    field a : A
