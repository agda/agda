-- Andreas, 2017-02-13, issue #2456 reported by identicalsnowflake
-- Introduced by fix for #1698

record Class (t : Set) : Set where

postulate
  t : Set

  instance Class t

-- Should give error, but not internal error.

-- Error (#2456): Unexpected declaration.

-- Error (PR #8000): [Syntax.WrongContentBlock]
-- A 'postulate' block can only contain type signatures, possibly
-- under keywords 'instance' and 'private'
