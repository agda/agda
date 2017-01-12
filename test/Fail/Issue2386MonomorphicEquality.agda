-- Andreas, 2017-01-12, issue #2386

postulate
  A : Set

data _≡_ (x : A) : A → Set where
  refl : x ≡ x

{-# BUILTIN EQUALITY _≡_ #-}

-- Monomorphic equality is not accepted.

-- If needed, this could change in the future.
