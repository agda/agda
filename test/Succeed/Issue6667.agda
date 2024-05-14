-- Andreas, 2024-03-01, issue #6667
-- Reported by @Soares, MWE by @szumixie

postulate
  A : Set
  F : Set → Set

-- Nullary syntax definition caused internal error in scope checker.

syntax A = S

B = F S

-- WAS: internal error.

-- Should succeed.
