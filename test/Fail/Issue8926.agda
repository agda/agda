-- Andreas, 2026-11-18, issue #8926
-- When we rename to an operator, we no longer keep the original @syntax@.

module Issue8926 where

module M where
  data N : Set where
    zero : N
    suc : N → N

  syntax suc x = x +1

open M using (N; zero) renaming (suc to infixl 42 _↑)

old-syntax : N
old-syntax = zero +1

-- Expected error: [NotInScope]
-- Not in scope:
--   +1 at ...
-- when scope checking +1
