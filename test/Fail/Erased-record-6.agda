record @0 R : Set₁ where
  field
    A : Set

  B : Set
  B = A

-- R.B should be erased.

_ : R → Set
_ = R.B
