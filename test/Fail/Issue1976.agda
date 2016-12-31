-- Andreas, 2016-12-31, issue #1976 raised by nad
-- Check for correct parameters in projection pattern

-- {-# OPTIONS -v tc.lhs.split:40 #-}

postulate
  A B : Set

module M (_ : Set) where

  record R : Set₂ where
    field
      F : Set₁

  open R public

open M A

wrong : M.R B
F wrong = Set

-- Expected error:
-- A != B of type Set
-- when checking that the clause F wrong = Set has type M.R B
