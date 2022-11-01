record @0 R : Set₁ where
  A : Set₁
  A = Set

  field
    B : Set

-- R.A should be erased.

_ : R → Set₁
_ = λ r → R.A r
