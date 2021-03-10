-- Andreas, 2020-11-16, issue #5055, reported by nad
-- Internal error caused by record pattern on pattern synonym lhs
-- (unreleased regression in 2.6.2).

open import Agda.Builtin.Sigma

data Shape : Set where
  c : Shape → Shape

pattern p (s , v) = c s , v

-- Should give some parse error or other controlled error.

-- Illegal pattern synonym argument  _ @ (s , v)
-- (Arguments to pattern synonyms cannot be patterns themselves.)
-- =<ERROR>
--  c s , v
