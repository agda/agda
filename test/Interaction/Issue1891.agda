-- Andreas, 2016-06-20, issue #1891

-- Computation of which variables are splittable was wrong
-- in the presence of a where-module.

-- {-# OPTIONS -v interaction.case:20 #-}

data D : Set where
  c : D

test : (x : D) → D
test x = {!x!}  -- C-c C-c
  where
   y = c

-- WAS:
-- Splitting on x reports:
-- Not a (splittable) variable: x
-- when checking that the expression ? has type D

-- Should work now.

-- Further tests:

record R (A : Set) : Set where
  testR : (x : D) → D
  testR x = {!x!}
    where B = A

module M (A : Set) where
  testM : (x : D) → D
  testM x = {!x!}
    where open R {A = A}
