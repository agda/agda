-- Andreas, 2016-12-31, re issue #1976
-- Allow projection pattern disambiguation by parameters

postulate
  A B : Set

module M (_ : Set) where

  record R : Set₂ where
    field
      F : Set₁

  open R public

module ShouldFail where
  open M _
  open M A

  test : M.R B
  F test = Set
