-- Andreas, 2024-10-06, issue #7533 reported by James McKinna, test by Szumi Xie.
-- DISPLAY pragmas should be like REWRITE rules, not like functions defined by pattern matching.
-- In particular, all names (not just constructors) should be matchable.

data Empty : Set where

postulate
  F : Set → Set
  X : Set
  A : Set

-- The following display form used to rewrite F _ to X.
-- Now it should only rewrite F Empty to X.

{-# DISPLAY F Empty = X #-}

_ : F Empty → F A
_ = F Empty

-- This is ill-typed, we are only interested in the printing
-- of the involved terms in the error message.

-- Error: Set !=< X → F A
-- when checking that the expression F Empty has type X → F A

-- Agda-2.7 prints X instead of F A.
