module Issue417 where

data _≡_ (A : Set₁) : Set₁ → Set₂ where
  refl : A ≡ A

abstract

  A : Set₁
  A = Set

  unfold-A : A ≡ Set
  unfold-A = refl

-- The result of inferring the type of unfold-A is the following:
--
--   Set ≡ Set
