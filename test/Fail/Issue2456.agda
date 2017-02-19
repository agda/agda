-- Andreas, 2017-02-13, issue #2456 reported by identicalsnowflake
-- Introduced by fix for #1698

record Class (t : Set) : Set where

postulate
  t : Set

  instance Class t

-- Should give error, but not internal error.
