{-# OPTIONS --erasure #-}

-- Andreas, 2018-10-16, runtime erasure

id : (@0 A : Set) (@0 x : A) → A
id A x = x

-- Expected error:
--
-- Variable x is declared erased, so it cannot be used here
-- when checking that the expression x has type A
