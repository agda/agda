-- Andreas, 2025-07-10, issue #7987.
-- Allow erased record matches in let.

{-# OPTIONS --erasure #-}

open import Agda.Builtin.Sigma

split2 : {A B C : Set} (@0 p : Σ A λ _ → B) (k : @0 A → @0 B → C) → C
split2 p k = let (x , y) = p in k x y

-- Expected error: [VariableIsErased]
-- Variable p is declared erased, so it cannot be used here
-- when inferring the type of p
