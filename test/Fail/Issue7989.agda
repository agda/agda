-- Andreas, 2025-07-09, issue #7989
-- Parse irrelevance in simple clauses ("aliases")

{-# OPTIONS --irrelevant-projections #-}

f : .(I : Set) → Set₁
f I = Set
  where
    D : Set
    .D = I

-- EXPECTED:
--
-- warning: -W[no]DivergentModalityInClause
-- Ignoring the modality . of the clause that diverges from the
-- declared modality of the function
--
-- error: [VariableIsIrrelevant]
-- Variable I is declared irrelevant, so it cannot be used here
-- when checking that the expression I has type Set
