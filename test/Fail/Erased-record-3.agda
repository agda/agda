{-# OPTIONS --erasure #-}

record @0 R : Set₂ where
  field
    x : Set₁

_ : R → R
_ = λ r → record r { x = Set }
