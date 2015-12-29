-- Andreas, 2015-12-29

record ⊤ : Set where

data P : ⊤ → Set where
  c : P record{}

test : (x : ⊤) (p : P x) → Set
test _ c with Set
test x y | z = ⊤

-- Expected error: with-clause pattern mismatch.
-- The error should be printed nicely, like:
--
-- With clause pattern x is not an instance of its parent pattern
-- record {}
-- when checking that the clause
-- test c with Set
-- test x y | z = ⊤
-- has type (x : ⊤) → P x → Set
