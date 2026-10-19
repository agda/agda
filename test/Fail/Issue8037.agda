-- Andreas, 2025-11-17, issue #8037, report and test case by Amy.
-- Checking projection pattern parameters only works
-- if during a module application we always copy the record type
-- along with any of its fields.

-- {-# OPTIONS -v tc.lhs.split:40 #-}

postulate
  A B : Set

module M (X : Set) where

  record R : Set₂ where
    field
      F : Set₁

  open R public

open M A using (F)  -- not importing R defeated the fix of #1976

wrong : M.R B
wrong .F = Set

-- Expected error: [UnequalTerms]
-- A != B of type Set
-- when checking the clause left hand side
-- wrong .F
