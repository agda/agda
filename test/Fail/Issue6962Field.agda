module Issue6962Field where

record R : Set₁ where
  field
    f (A : Set) : A -> A
