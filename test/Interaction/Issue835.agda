
module Issue835 where

data _≡_ {A : Set} (x : A) : A → Set where
  refl : x ≡ x

postulate
  A : Set
  x y : A

F : x ≡ y → Set
F ()

