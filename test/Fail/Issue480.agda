-- Andreas, 2016-02-02

module _ where

  data Q : Set where
    a : Q

  data Overlap : Set where
    a : Overlap

  postulate helper : ∀ {T : Set} → (T → T) → Set

  test₃ : Set
  test₃ = helper λ { a → a }

-- Does not succeed, as the type of the extended lambda is ambiguous.
-- It should fail with an error or unsolved metas instead of
-- looping the type checker.
