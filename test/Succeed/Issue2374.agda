-- Andreas, 2016-12-31, issue #2374
-- Use hiding info to disambiguate overloaded projections.

-- {-# OPTIONS -v tc.lhs.split:40 #-}

postulate A B : Set

module M where

  record R : Set₂ where
    field
      F : Set₁

module Order1 where
  open M.R
  open M.R {{...}}

  test : M.R
  F test = Set

  inst : M.R
  F {{inst}} = Set

module Order2 where
  open M.R {{...}}
  open M.R

  test : M.R
  F test = Set

  inst : M.R
  F {{inst}} = Set

module N (A : Set) where

  record R : Set₂ where
    field
      F : Set₁

module Par1 where
  open N.R {A = A}
  module RB = N.R {A = B}; open RB {{...}}

  test : N.R A
  F test = Set

  inst : N.R B
  F {{inst}} = Set

module Par2 where
  module RA = N.R {A = A}; open RA {{...}}
  open N.R {A = B}

  test : N.R B
  F test = Set

  inst : N.R A
  F {{inst}} = Set

-- All should be accepted.
