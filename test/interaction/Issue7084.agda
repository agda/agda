
module _ (X : Set) where

  record R : Set₁ where
    field t : X

  auto : R → X
  auto r = {!!}
