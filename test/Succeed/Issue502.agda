
module Issue502 where

record R : Set where
  record S (A : Set) : Set where
    field
      f : A → A
