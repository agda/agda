-- Andreas, 2016-12-29, issue #2366
-- With clauses need to be printed in fresh environment,
-- as they DON'T shadow the pattern variables of the parent clause.
-- (These are not even in scope)

-- {-# OPTIONS -v error.checkclause:60 #-}

open import Agda.Builtin.List

test : {A : Set} → List A → List A
test (x ∷ y ∷ ys) with []
test (x ∷ []) | q = []
test _ = []

-- ERROR WAS:
-- With clause pattern xs is not an instance of its parent pattern y ∷ ys
-- when checking that the clause
-- test (x ∷ y ∷ ys) with []
-- test (x₁ ∷ xs) | q = []
-- has type {A : Set} → List A → List A
-- NOTE THE x₁!

-- Expected error:
-- With clause pattern xs is not an instance of its parent pattern y ∷ ys
-- when checking that the clause
-- test (x ∷ y ∷ ys) with []
-- test (x ∷ xs) | q = []
-- has type {A : Set} → List A → List A

-- Jesper, 2018-05-14: the old test case is now accepted by Agda,
-- so I had to change it slightly to test we are still printing
-- a proper error message:
-- With clause pattern [] is not an instance of its parent pattern
-- y ∷ ys
-- when checking that the clause
-- test (x ∷ y ∷ ys) with []
-- test (x ∷ []) | q = []
-- has type {A : Set} → List A → List A
