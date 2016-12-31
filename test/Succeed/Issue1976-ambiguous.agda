-- Andreas, 2016-12-31, re issue #1976
-- Allow projection pattern disambiguation by parameters

-- {-# OPTIONS -v tc.lhs.split:40 #-}

postulate
  A B : Set

module M (_ : Set) where

  record R : Set₂ where
    field
      F : Set₁

  open R public

module Order1 where
  open M A
  open M B

  test : M.R B
  F test = Set

module Order2 where
  open M B
  open M A

  test : M.R B
  F test = Set

-- should succeed
