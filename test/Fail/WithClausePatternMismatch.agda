-- Andreas, 2015-12-29

record ⊤ : Set where

data P : ⊤ → Set where
  c : P record{}
  d : P record{}

test : (x : ⊤) (p : P x) → Set
test _ c with Set
test _ d | z = ⊤

-- Expected error: with-clause pattern mismatch.
-- The error should be printed nicely, like:
--
-- With clause pattern d is not an instance of its parent pattern c
-- when checking that the clause
-- test _ c with Set
-- test _ d | z = ⊤
-- has type (x : ⊤) → P x → Set
