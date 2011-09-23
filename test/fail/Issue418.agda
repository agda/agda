-- {-# OPTIONS -v tc.meta:25 #-}
module Issue418 where

data _≡_ (A : Set₁) : Set₁ → Set₂ where
  refl : A ≡ A

abstract

  A : Set₁
  A = Set

  unfold-A : A ≡ _
  unfold-A = refl

-- I don't think we should solve the meta-variable corresponding to
-- the underscore above. We have two obvious choices, A and Set, and
-- these choices are not equivalent.

-- Andreas, 2011-05-30
-- Meta-Variable should remain unsolved
 