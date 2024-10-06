-- Andreas, 2024-10-06, issue #7533 reported by James McKinna, test by Szumi Xie

data Empty : Set where

postulate
  F : Set → Set
  X : Set
  A : Set

-- The following display form will rewrite F _ to X.
-- Probably the user intended onto to rewrite F Empty to X.
-- In this case, we can alert the user that Empty is bound
-- on the lhs but unused on the rhs, indicating a problem.

{-# DISPLAY F Empty = X #-}

-- Expected warning: UnusedVariablesInDisplayForm

_ : F A
_ = A

-- This is ill-typed, we are only interested in the printing
-- of the involved terms in the error message.
