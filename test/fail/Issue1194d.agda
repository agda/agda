-- Andreas, 2014-09-23
-- Issue 1194, reported by marco.vax91, 2014-06-13

-- {-# OPTIONS -v scope.operators:50 #-}

module _ where

module A where

  data D1 : Set where
    c : D1

  -- Non-default fixity here.
  infix 99 c

module B where

  data D2 : Set where
    c : A.D1 → D2

  -- Interesting notation for c here.
  syntax c x = ⟦ x ⟧

open A
open B

-- Since there are two non-default fixities/notations for c in scope
-- we should not be able to use any one.

test : D2
test = ⟦ c ⟧

-- Should fail.
