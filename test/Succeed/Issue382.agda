-- Andreas, 2016-07-19 issue #382, duplicate of #278
-- report and test case by Nisse, 2011-01-30

module Issue382 {A : Set} where

data _≡_ (x : A) : A → Set where
  refl : x ≡ x

abstract

  id : A → A
  id x = y
    where
      y : A
      y = x

  lemma : ∀ x → id x ≡ x
  lemma x = refl

-- should succeed
