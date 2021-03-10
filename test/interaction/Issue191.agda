-- Andreas, 2020-02-11 reopened issue
-- Andreas, 2016-06-20 closed issue
-- Issue #191, reported 2009-12-02 by Nisse

-- {-# OPTIONS -v tc.cover.isCovered:20 #-}

data T (A : Set) : Set → Set1 where
  c₁ : {B : Set} → T A B
  c₂ :             T A A

foo : {A B C : Set} → T A (B → C) → T A B → Set₁
foo c₁ y = Set
foo x  y = {! y !}

-- WAS:
-- Perform the indicated case split. Agda will happily replace the
-- last clause with two separate clauses, one for each constructor
-- of T, but the resulting file is not type correct:

-- Bug.agda:8,1-10,13
-- Cannot split on the constructor c₂
-- when checking the definition of foo

-- In this case Agda should not modify the source file, it is
-- preferable to just give an error indicating that the split cannot
-- be performed.

---------------------------------------------------------------------------

-- THEN (Agda-2.5.2):
-- I'm not sure if there should be a case for the constructor c₂,
-- because I get stuck when trying to solve the following unification
-- problems (inferred index ≟ expected index):
--   A ≟ A → C
-- when checking that the expression ? has type Set₁

-- Current behavior (not splitting) is correct.

---------------------------------------------------------------------------

-- NOW: PR #3973 brings back the old faulty behavior.
-- The fix in Agda 2.5.2 was only accidential.

-- Agda now puts in the two clauses:
--
--   foo x c₁ = ?
--   foo x c₂ = ?
--
-- and then complains upon reload:
--
--   I'm not sure if there should be a case for the constructor c₂,
--   because I get stuck when trying to solve the following unification
--   problems (inferred index ≟ expected index):
--     B → C ≟ B
--   Possible reason why unification failed:
--     Cannot solve variable B of type Set with solution B → C because the
--     variable occurs in the solution, or in the type of one of the
--     variables in the solution.
--   when checking the definition of foo
