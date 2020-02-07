-- Andreas, 2020-01-28, issue #4399
-- Pattern @{{_ = p}}@ should not be parsed as cubical partial split.

postulate
  A : Set

data T : Set where
  tt : T

f : {x : A} {{_ : T}} → Set
f ⦃ _ = tt ⦄ = A

-- Expected: Parse error
-- Not a valid named argument: _ = tt
