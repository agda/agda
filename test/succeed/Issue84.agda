
module Issue84 where

data _≡_ {a : Set} (x : a) : a -> Set where
  refl : x ≡ x

data D : Set where
  d₁ : D
  d₂ : D

foo : D -> d₁ ≡ d₂ -> Set
foo d₁ eq ~ D
foo d₂ eq with eq
foo d₂ eq | ()

-- Not implemented: mutual recursion and corecursion
