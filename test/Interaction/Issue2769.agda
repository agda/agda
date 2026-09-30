-- Andreas, 2017-10-11, issue #2769

-- Patch https://github.com/agda/agda/commit/7fc73607703e0373beaf65ba05fb1911b6d84a5e
--
--   Re #2495: make mutual info safer by distinguishing Nothing and Just []
--
--   Nothing means: never computed.
--   Just [] means: computed, but non-recursive.
--
--   These two notions were conflated before.
--
-- introduced this regression because the projection-likeness check failed.

-- {-# OPTIONS --show-implicit #-}
-- {-# OPTIONS -v 10 #-}
-- {-# OPTIONS -v tc.signature:60 #-}
-- {-# OPTIONS -v tc.mod.apply:80 #-}
-- {-# OPTIONS -v tc.sig.param:90 #-}
-- {-# OPTIONS -v tc.display:100 #-}


module Issue2769 where

module M (_X : Set₁)
  where

  record R (_Y : Set₂) : Set₁ where
    field A : Set

  record S : Set₁ where
    field r : R Set₁
    module Rr = R r

ok : (s : M.S Set) → M.R.A (M.S.r s) -- M.S.Rr.A s
ok = {!!}  -- goal displayed as  (s : M.S Set) → M.R.A (M.S.r s)

module MSet = M Set

goal : (s : M.S Set) → M.R.A (M.S.r s) -- M.S.Rr.A s
goal = {!!}  -- WAS: goal displayed as  (s : MSet.S) → MSet.S.Rr.A

-- adding display form Issue2769.M.R.A --> Issue2769.MSet.S.Rr.A
-- Display {dfFreeVars = 1, dfPats = [Apply ru(Def Issue2769.M.S.r [Apply ru(Var 0 [])])], dfRHS = DTerm (Def Issue2769.MSet.S.Rr.A [])}

-- EXPECTED:
-- Should display goal 1 as
-- ?1 : (s : MSet.S) → M.R.A (MSet.S.r s)

-- AFTER FIXING #4857:
-- ?1 : (s : MSet.S) → MSet.S.Rr.A s
