module _ where

module @0 M where

  A : Set₁
  A = Set

record R : Set₂ where
  field
    A : Set₁

r : R
r = record { M }
