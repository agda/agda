{-# OPTIONS --cubical #-}

F : Set → Set
F A = A

record R : Set₁ where
  field
    A : Set

r : Set → R
r A = λ where
  .R.A → A
