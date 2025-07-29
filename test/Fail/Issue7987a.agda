-- Andreas, 2025-07-10, issue #7987.
-- Allow erased record matches in let.

{-# OPTIONS --erasure #-}

open import Agda.Builtin.Sigma

split2 : {A B C : Set} (@0 p : Σ A λ _ → B) (k : A → B → C) → C
split2 p k = let @0 (x , y) = p in k x y

-- Expected error: [VariableIsErased]
-- Variable x is declared erased, so it cannot be used here
-- when checking that the expression x has type A
