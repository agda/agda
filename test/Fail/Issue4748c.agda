{-# OPTIONS --cubical-compatible #-}

postulate
  A : Set
  B : A → Set

-- fine
record R₀ : Set where
  field
    @0 x : A
    @0 y : B x

-- bad
record R : Set where
  field
    @0 x : A
    y : B x
