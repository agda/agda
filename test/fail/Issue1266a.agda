-- Andreas, 2014-09-02
-- Up to today, there was no implementation of shadowing local variables
-- (e.g., λ-bound variables) by local imports.

-- {-# OPTIONS -v scope.locals:10 #-}

module _ where

module M where

  A = Set1

test : (A : Set) → let open M in A
test A = Set

-- The A exported by M is in competition with the local A.
-- Ambiguous name should be reported.
