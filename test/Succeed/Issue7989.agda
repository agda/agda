-- Andreas, 2025-07-09, issue #7989
-- Parse irrelevance in simple clauses ("aliases")

{-# OPTIONS --irrelevant-projections #-}

f : .(I : Set) → Set₁
f I = Set
  where
    .A = I

    .B : Set
    B = I

    .C : Set
    .C = I
