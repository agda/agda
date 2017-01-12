-- Andreas, 2017-01-12, issue #2386

postulate
  B : Set

data _≡_ {A B : Set} (x : A) : A → Set where
  refl : (b : B) → x ≡ x

{-# BUILTIN EQUALITY _≡_ #-}

-- Wrong type of _≡_
