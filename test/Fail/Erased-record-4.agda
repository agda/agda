{-# OPTIONS --erasure #-}

record @0 R : Set₁ where
  field
    x : Set

_ : Set₁
_ = R
