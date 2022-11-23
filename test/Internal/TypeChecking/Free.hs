{-# LANGUAGE TemplateHaskell #-}

-- | Tests for free variable computations.

module Internal.TypeChecking.Free ( tests ) where

import Agda.Syntax.Common
import Agda.Syntax.Internal

import Agda.TypeChecking.Free (freeIn, freeVars)
import Agda.TypeChecking.Free.Lazy

import Agda.Utils.Singleton

import qualified Data.IntMap as Map
import Data.Monoid

import Internal.Helpers
import Internal.TypeChecking.Free.Lazy ()

------------------------------------------------------------------------------
-- * Semiring properties of 'FlexRig' with empty 'MetaSet'

type FlexRig0 = FlexRig' ()

-- ** 'addFlexRig' forms an commutative (additive) monoid
-- with zero (neutral) 'Flexible' and infinity (absorptive element) 'StronglyRigid'

prop_addFlexRig0_associative :: Prop3 FlexRig0
prop_addFlexRig0_associative = isAssociative addFlexRig

prop_addFlexRig0_commutative :: Prop2 FlexRig0
prop_addFlexRig0_commutative = isCommutative addFlexRig

prop_addFlexRig0_neutral :: Prop1 FlexRig0
prop_addFlexRig0_neutral = isIdentity zeroFlexRig addFlexRig

prop_addFlexRig0_absorptive :: Prop1 FlexRig0
prop_addFlexRig0_absorptive = isZero omegaFlexRig addFlexRig

-- ** 'composeFlexRig' forms an idempotent commutative monoid with
-- unit 'Unguarded' and zero 'Flexible'

prop_composeFlexRig0_associative :: Prop3 FlexRig0
prop_composeFlexRig0_associative = isAssociative composeFlexRig

prop_composeFlexRig0_commutative :: Prop2 FlexRig0
prop_composeFlexRig0_commutative = isCommutative composeFlexRig

prop_composeFlexRig0_idempotent :: Prop1 FlexRig0
prop_composeFlexRig0_idempotent = isIdempotent composeFlexRig

prop_composeFlexRig0_zero :: Prop1 FlexRig0
prop_composeFlexRig0_zero = isZero zeroFlexRig composeFlexRig

prop_composeFlexRig0_unit :: Prop1 FlexRig0
prop_composeFlexRig0_unit = isIdentity oneFlexRig composeFlexRig

-- ** 'composeFlexRig' distributes over 'addFlexRig'

prop_FlexRig0_distributive :: Prop3 FlexRig0
prop_FlexRig0_distributive = isDistributive composeFlexRig addFlexRig

-- Not true (I did not expect it to be true, just for sanity I checked):
-- prop_FlexRig_distributive' = isDistributive addFlexRig composeFlexRig

------------------------------------------------------------------------------
-- * Properties of 'FlexRig'

-- ** 'addFlexRig' forms an commutative (additive) monoid
-- with zero (neutral) 'Flexible' and infinity (absorptive element) 'StronglyRigid'

prop_addFlexRig_associative :: Prop3 FlexRig
prop_addFlexRig_associative = isAssociative addFlexRig

prop_addFlexRig_commutative :: Prop2 FlexRig
prop_addFlexRig_commutative = isCommutative addFlexRig

prop_addFlexRig_neutral :: Prop1 FlexRig
prop_addFlexRig_neutral = isIdentity zeroFlexRig addFlexRig

prop_addFlexRig_absorptive :: Prop1 FlexRig
prop_addFlexRig_absorptive = isZero omegaFlexRig addFlexRig

-- ** 'composeFlexRig' forms an idempotent commutative monoid with
-- unit 'Unguarded' and zero 'Flexible'

prop_composeFlexRig_associative :: Prop3 FlexRig
prop_composeFlexRig_associative = isAssociative composeFlexRig

prop_composeFlexRig_commutative :: Prop2 FlexRig
prop_composeFlexRig_commutative = isCommutative composeFlexRig

prop_composeFlexRig_idempotent :: Prop1 FlexRig
prop_composeFlexRig_idempotent = isIdempotent composeFlexRig

-- -- Not a zero for multiplication since it does not empty or flood (with everything)
-- -- the MetaSet in Flexible.
-- prop_composeFlexRig_zero :: Prop1 FlexRig
-- prop_composeFlexRig_zero = isZero zeroFlexRig composeFlexRig

prop_composeFlexRig_unit :: Prop1 FlexRig
prop_composeFlexRig_unit = isIdentity oneFlexRig composeFlexRig

-- -- Distributivity fails with non-empty Flex MetaSets.
-- -- Counterexample:
-- --
-- --   LHS: Flex ms * (Flex ns + SRig) = Flex ms * SRig = Flex ms
-- --   RHS: Flex ms * Flex ns + Flex ms * SRig = Flex (ms ++ ns) + Flex ms = Flex (ms ++ ns)

-- prop_FlexRig_distributive :: Prop3 FlexRig
-- prop_FlexRig_distributive = isDistributive composeFlexRig addFlexRig

------------------------------------------------------------------------------
-- * Semiring properties of 'VarOcc' with empty 'MetaSet'

type VarOcc0 = VarOcc' ()

-- ** Commutative (additive) 'Monoid' 'VarOcc0'

prop_Monoid_VarOcc0 :: Property3 VarOcc0
prop_Monoid_VarOcc0 = isMonoid

prop_Monoid_VarOcc0_commutative :: Prop2 VarOcc0
prop_Monoid_VarOcc0_commutative = isCommutative mappend

-- | Absorbtive element.
prop_topVarOcc0 :: VarOcc0 -> Bool
prop_topVarOcc0 = isZero topVarOcc mappend

-- ** 'composeVarOcc' forms a commutative monoid with unit 'oneVarOcc' and zero
-- 'mempty'

prop_composeVarOcc0_associative :: Prop3 VarOcc0
prop_composeVarOcc0_associative = isAssociative composeVarOcc

prop_composeVarOcc0_commutative :: Prop2 VarOcc0
prop_composeVarOcc0_commutative = isCommutative composeVarOcc

-- This is not true anymore, now that we have non-idempotent modalities
-- prop_composeVarOcc0_idempotent :: Prop1 VarOcc0
-- prop_composeVarOcc0_idempotent = isIdempotent composeVarOcc

prop_composeVarOcc0_zero :: Prop1 VarOcc0
prop_composeVarOcc0_zero = isZero mempty composeVarOcc

prop_composeVarOcc0_unit :: Prop1 VarOcc0
prop_composeVarOcc0_unit = isIdentity oneVarOcc composeVarOcc

-- ** 'composeVarOcc' distributes over 'mappend'

-- | @*@ (composition) distributes over @+@ (aggregation).
prop_VarOcc0_distributive :: Prop3 VarOcc0
prop_VarOcc0_distributive = isDistributive composeVarOcc mappend

------------------------------------------------------------------------------
-- * Properties of 'VarOcc'

-- ** Commutative (additive) 'Monoid' 'VarOcc'

prop_Monoid_VarOcc :: Property3 VarOcc
prop_Monoid_VarOcc = isMonoid

prop_Monoid_VarOcc_commutative :: Prop2 VarOcc
prop_Monoid_VarOcc_commutative = isCommutative mappend

-- | Absorbtive element.
prop_topVarOcc :: VarOcc -> Bool
prop_topVarOcc = isZero topVarOcc mappend

-- ** 'composeVarOcc' forms an commutative monoid with
-- unit 'oneVarOcc'

prop_composeVarOcc_associative :: Prop3 VarOcc
prop_composeVarOcc_associative = isAssociative composeVarOcc

prop_composeVarOcc_commutative :: Prop2 VarOcc
prop_composeVarOcc_commutative = isCommutative composeVarOcc

-- This is not true anymore, now that we have non-idempotent modalities
-- prop_composeVarOcc_idempotent :: Prop1 VarOcc
-- prop_composeVarOcc_idempotent = isIdempotent composeVarOcc

-- -- Caveat: not a zero for multiplication in general
-- -- since it does not empty or flood (with everything) the MetaSet in Flexible.
-- prop_composeVarOcc_zero :: Prop1 VarOcc
-- prop_composeVarOcc_zero = isZero mempty composeVarOcc

prop_composeVarOcc_unit :: Prop1 VarOcc
prop_composeVarOcc_unit = isIdentity oneVarOcc composeVarOcc

-- -- FAILS for non-empty 'MetaSet', see prop_FlexRig_distributive
-- -- | @*@ (composition) distributes over @+@ (aggregation).
-- prop_VarOcc_distributive :: Prop3 VarOcc
-- prop_VarOcc_distributive = isDistributive composeVarOcc mappend

------------------------------------------------------------------------------
-- * Semimodule properties of 'VarMap' with empty 'MetaSet'

type VarMap0 = VarMap' ()

-- ** Commutative (additive) 'Monoid' 'VarMap0'

prop_Monoid_VarMap0 :: Property3 VarMap0
prop_Monoid_VarMap0 = isMonoid

prop_Monoid_VarMap0_commutative :: Prop2 VarMap0
prop_Monoid_VarMap0_commutative = isCommutative mappend

-- ** Left semimodule for 'VarOcc0'

-- Distributivity fails with non-empty 'MetaSet':

prop_isAlmostSemimodule0_withVarOcc :: VarOcc0 -> VarOcc0 -> Property2 VarMap0
prop_isAlmostSemimodule0_withVarOcc = isAlmostSemimodule oneVarOcc composeVarOcc withVarOcc

-- The semimodule property can be broken down into the following properties:

prop_isSemimodule0_withVarOcc1 :: VarOcc0 -> Property2 VarMap0
prop_isSemimodule0_withVarOcc1 r = isMonoidMorphism (withVarOcc r)

prop_isSemimodule0_withVarOcc2 :: VarMap0 -> Prop2 VarOcc0
prop_isSemimodule0_withVarOcc2 m = isSemigroupMorphism (`withVarOcc` m)

-- Not a proper semimodule, since this unit law fails:
-- prop_isSemimodule0_withVarOcc2_unit :: Prop1 VarMap0
-- prop_isSemimodule0_withVarOcc2_unit m = withVarOcc empty m == empty

prop_isSemimodule0_withVarOcc3a :: Prop1 VarMap0
prop_isSemimodule0_withVarOcc3a m =
  withVarOcc oneVarOcc m == m

prop_isSemimodule0_withVarOcc3b :: VarMap0 -> Prop2 VarOcc0
prop_isSemimodule0_withVarOcc3b m r s =
  withVarOcc (r `composeVarOcc` s) m == withVarOcc r (withVarOcc s m)

------------------------------------------------------------------------------
-- * Properties of 'VarMap'

-- ** Commutative (additive) 'Monoid' 'VarMap'

prop_Monoid_VarMap :: Property3 VarMap
prop_Monoid_VarMap = isMonoid

prop_Monoid_VarMap_commutative :: Prop2 VarMap
prop_Monoid_VarMap_commutative = isCommutative mappend

-- ** Left semimodule for 'VarOcc' (fails for non-empty 'MetaSet')

-- -- Distributivity fails with non-empty 'MetaSet':

-- prop_isAlmostSemimodule_withVarOcc :: VarOcc -> VarOcc -> Property2 VarMap
-- prop_isAlmostSemimodule_withVarOcc = isAlmostSemimodule oneVarOcc composeVarOcc withVarOcc

-- The semimodule property can be broken down into the following properties:

-- -- Distributivity fails with non-empty 'MetaSet':

-- prop_isSemimodule_withVarOcc1 :: VarOcc -> Property2 VarMap
-- prop_isSemimodule_withVarOcc1 r = isMonoidMorphism (withVarOcc r)

-- prop_isSemimodule_withVarOcc2 :: VarMap -> Prop2 VarOcc
-- prop_isSemimodule_withVarOcc2 m = isSemigroupMorphism (`withVarOcc` m)

-- prop_isSemimodule_withVarOcc2_mult :: VarMap -> Prop2 VarOcc
-- prop_isSemimodule_withVarOcc2_mult m r s = withVarOcc (r <> s) m == withVarOcc r m <> withVarOcc s m

-- Not a proper semimodule, since this unit law fails:
-- prop_isSemimodule_withVarOcc2_unit :: Prop1 VarMap
-- prop_isSemimodule_withVarOcc2_unit m = withVarOcc empty m == empty

prop_isSemimodule_withVarOcc3a :: Prop1 VarMap
prop_isSemimodule_withVarOcc3a m =
  withVarOcc oneVarOcc m == m

prop_isSemimodule_withVarOcc3b :: VarMap -> Prop2 VarOcc
prop_isSemimodule_withVarOcc3b m r s =
  withVarOcc (r `composeVarOcc` s) m == withVarOcc r (withVarOcc s m)

------------------------------------------------------------------------------
-- * Unit tests

prop_freeIn :: Bool
prop_freeIn = all (0 `freeIn`)
  [ var 0
  , Lam defaultArgInfo $ Abs "x" $ var 1
  , Sort $ varSort 0
  ]

-- One semimodule unit law fails, since withVarOcc is pointwise application
-- of the context to the variable set.
-- (Even for the zero context, the variable set is not cleared.)
prop_isSemimodule_counterexample :: Prop1 VarOcc
prop_isSemimodule_counterexample o = withVarOcc mempty m /= mempty
  where m = VarMap $ Map.fromList [(0,o)]

prop_isSemimodule_withVarOcc1_counterexample :: Bool
prop_isSemimodule_withVarOcc1_counterexample =
  withVarOcc r (m <> m') /=           -- LHS: Flexible [1]
  withVarOcc r m <> withVarOcc r m'   -- RHS: Flexible [1,2]
  where
    occ o  = VarOcc o unitModality
    rig    = occ Unguarded
    flex n = occ $ Flexible $ singleton $ MetaId n (ModuleNameHash 0)
    r      :: VarOcc
    r      = flex 1
    m, m'  :: VarMap
    m      = VarMap $ singleton (0, rig)
    m'     = VarMap $ singleton (0, flex 2)

prop_isSemimodule_withVarOcc2_counterexample :: Bool
prop_isSemimodule_withVarOcc2_counterexample =
  withVarOcc (r <> s) m /=
  withVarOcc r m <> withVarOcc s m
  where
    occ o  = VarOcc o unitModality
    flex n = occ $ Flexible $ singleton $ MetaId n (ModuleNameHash 0)
    r, s   :: VarOcc
    r      = flex 1
    s      = occ StronglyRigid
    m      :: VarMap
    m      = VarMap $ singleton (0, flex 2)

prop_isSemimodule_withVarOcc2_not_a_counterexample :: Bool
prop_isSemimodule_withVarOcc2_not_a_counterexample =
  withVarOcc (r <> s) m ==
  withVarOcc r m <> withVarOcc s m
  where
    occ r = VarOcc StronglyRigid $ Modality r topQuantity topCohesion topPolarity
    r, s  :: VarOcc
    r     = occ irrelevant
    s     = occ shapeIrrelevant
    m     :: VarMap
    m     = VarMap $ Map.fromList [(0, occ irrelevant)]
  -- LHS:
  --   r <> s                = min Irrelevant ShapeIrrelevant = ShapeIrrelevant
  --   withVarOcc (r <> s) m = max ShapeIrrelevant Irrelevant = Irrelevant
  -- RHS:
  --   withVarOcc r m = max Irrelevant Irrelevant = Irrelevant
  --   withVarOcc s m = max ShapeIrrelevant  Irrelevant = Irrelevant
  --   withVarOcc r m <> withVarOcc s m
  --                  = min Irrelevant Irrelevant = Irrelevant

-- Sample term, TODO: expand to unit test.

ty :: Term
ty = Pi (defaultDom ab) $ Abs "x" $ El (Type $ Max 0 []) $ var 5
  where
    a  = El (Prop $ Max 0 []) $
           var 4
    b  = El (Type $ Max 0 []) $
           Sort $ Type $ Max 0 []
    ab = El (Type $ Max 1 []) $
           Pi (defaultDom a) (Abs "x" b)

------------------------------------------------------------------------
-- * All tests
------------------------------------------------------------------------

-- Template Haskell hack to make the following $allProperties work
-- under ghc-7.8.
return [] -- KEEP!

-- | All tests as collected by 'allProperties'.
--
-- Using 'allProperties' is convenient and superior to the manual
-- enumeration of tests, since the name of the property is added
-- automatically.

tests :: TestTree
tests = testProperties "Internal.TypeChecking.Free" $allProperties
