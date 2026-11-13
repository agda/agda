module Issue434AcrossField where

record R (A : Set) : Set where
  identity : A → A

  field a : A

  identity x = x
