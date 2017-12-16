-- Andreas, 2017-12-16, issue #2868.

-- Printing record fields correctly inside the record definition
-- in the presence of --postfix-projections.

{-# OPTIONS --postfix-projections #-}

open import Agda.Builtin.Equality

postulate
  A : Set

record R : Set where
  field
    a : A
    same : a ≡ a
  test : A
  test = same

-- (We are reifying  Var 0 [Proj ProjSystem Issue2868.R.a])

-- WAS:    .a ≡ .a !=< A of type Set    -- Note the extra dots!
-- Expected: a ≡ a !=< A of type Set
