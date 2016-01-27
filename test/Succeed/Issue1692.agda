-- Andreas, 2016-01-27
-- After complaints of Wolfram Kahl and Aaron Stump
-- we decided it is imported to keep the rewrite behavior
-- that does not rewrite in rewrite terms.

open import Common.Equality

test : ∀{A : Set}{a : A}{f : A → A} (p : f a ≡ a) → f (f a) ≡ a
test p rewrite p = p

-- rewrite should not happen in p itself,
-- otherwise we get  p : a ≡ a  which is useless.
