{-# OPTIONS --erasure #-}

record @0 R : Set₁ where
  field
    @ω A : Set

-- R.A should be erased.

_ : R → Set
_ = R.A
