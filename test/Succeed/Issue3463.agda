
record R : Set₁ where
  field
    A : Set

open R ⦃ … ⦄

-- The inferred type of A is ⦃ r : R ⦄ → Set. However, the following
-- code is rejected:

X : R → Set
X r = A ⦃ r = r ⦄

-- WAS: Function does not accept argument ⦃ r = r ⦄
-- when checking that ⦃ r = r ⦄ is a valid argument to a function of
-- type ⦃ r = r₁ : R ⦄ → Set

-- SHOULD: succeed
