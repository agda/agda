-- Andreas, 2016-10-09, issue #2223

-- The level constraint solver needs to combine constraints
-- from different contexts and modules.
-- The parameter refinement broke this test case.

-- {-# OPTIONS -v tc.with.top:25 #-}
-- {-# OPTIONS -v tc.conv.nat:40 #-}
-- {-# OPTIONS -v tc.constr.add:45 #-}

open import Common.Level

module _ (a ℓ : Level) where

module Function where

  mutual
    X : Level
    X = _  -- Agda 2.5.1.1 solves this level meta

    X<=a : Set (X ⊔ a) → Set a
    X<=a A = A

    test : Set₁
    test with (lsuc ℓ)
    ... | _ = Set

      where
        a<=X : Set (X ⊔ a) → Set X
        a<=X A = A

-- Should solve all metas.
