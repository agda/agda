
module Issue84 where

data _≡_ {a : Set} (x : a) : a -> Set where
  refl : x ≡ x

codata D : Set where
  d₁ : D
  d₂ : D

foo : D -> d₁ ≡ d₂ -> D
foo d₁ eq ~ d₁
foo d₂ eq with eq
foo d₂ eq | ()

-- Not implemented: mutual recursion and corecursion
