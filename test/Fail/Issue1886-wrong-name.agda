-- Andreas, 2016-12-30, issue #1886, reported by nad
--
-- Change of parameter names is an error.
-- Reason: the parameter names become names of hidden arguments
-- in the constructors.  There should be no ambiguity.

data D (X : Set) : Set

data D (Y : Set) where
  c : Y → D Y
