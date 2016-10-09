-- Andreas, 2016-10-09, issue #2223

-- The level constraint solver needs to combine constraints
-- from different contexts and modules.
-- The parameter refinement broke this test case.

-- {-# OPTIONS -v tc.with.top:25 #-}
-- {-# OPTIONS -v tc.conv.nat:40 #-}
-- {-# OPTIONS -v tc.constr.add:45 #-}

open import Common.Level

module _ (a ℓ : Level) where

  mutual
    X : Level
    X = _

    data D : Set (lsuc a) where
      c : Set X → D  -- X <= a

    test : Set₁
    test with (lsuc ℓ) -- failed
    ... | _ = Set
    -- test = Set -- works

      where
        data C : Set (lsuc X) where
          c : Set a → C -- a <= X

-- Should solve all metas.
