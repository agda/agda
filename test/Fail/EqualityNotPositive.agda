
-- Jesper, 2019-09-12: The fix of #3541 introduced a regression: the
-- index of the equality type is treated as a positive argument.

data _≡_ (A : Set) : Set → Set where
  refl : A ≡ A

postulate X : Set

data D : Set where
  c : X ≡ D → D
