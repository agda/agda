module Issue434FieldInExplicitMutual where

record R (A : Set) : Set where
  mutual
    identity : A → A
    field a : A
    identity x = x
