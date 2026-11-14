module Issue8916DuplicateFields where

record R : Set₁ where
  field A : Set
  opaque
    opaque
      field A : Set
      B : Set
      B = A
