-- Andreas, 2014-09-23
-- Issue 1194, reported by marco.vax91, 2014-06-13

-- {-# OPTIONS -v scope.operators:50 #-}

module _ where

module A where

  data D1 : Set where
    c : D1

  -- Just default notation for c here.

module B where

  data D2 : Set where
    c : A.D1 → D2

  -- Interesting notation for c here.
  syntax c x = ⟦ x ⟧

open A
open B

-- Since there is only one interesting notation for c in scope
-- we should be able to use it.

test : D2
test = ⟦ c ⟧
