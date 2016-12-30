-- Andreas, 2016-12-30, issue #1886, reported by nad
--
-- Omitted hidden parameters are not in scope.

postulate
  A : Set
  P : A → Set

data D {a} (X : P a) : Set₁

data D X where
  c : P a → D _

-- Expected error:
--
-- Not in scope: a
