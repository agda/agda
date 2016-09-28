-- Andreas, 2016-09-28, Level meta below neutral level
-- Agda previously simplified X <= a to X = a.
-- This loses the solution X = lzero.

-- {-# OPTIONS -v tc.constr.add:40 #-}

open import Common.Level

module _ (a : Level) where

module WorksWithSwappedDeclarations where

  mutual
    X : Level
    X = _

    data E : Set₁ where
      c : Set X → E  -- constraint lsuc X <= 1 solves X = lzero

    data D : Set (lsuc a) where
      c : Set X → D  -- fine since lzero <= a

module WorksWithGivenSolution where

  mutual
    X : Level
    X = lzero

    data D : Set (lsuc a) where
      c : Set X → D

    data E : Set₁ where
      c : Set X → E

module Test where

  mutual
    X : Level
    X = _

    data D : Set (lsuc a) where
      c : Set X → D  -- solved X (prematurely) since X <= a implies X = a ?? (Wrong!)

    data E : Set₁ where
      c : Set X → E  -- constraint X <= 0 became contradictory constraint a <= 0

-- ERROR WAS:
-- The type of the constructor does not fit in the sort of the
-- datatype, since Set (lsuc a) is not less or equal than Set₁
-- when checking the constructor c in the declaration of E

-- should succeed
