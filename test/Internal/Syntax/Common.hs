{-# LANGUAGE TemplateHaskell #-}

module Internal.Syntax.Common ( tests ) where

import Control.Applicative

import Agda.Syntax.Common
import Agda.Syntax.Position ( noRange )

import Internal.Helpers

------------------------------------------------------------------------------
-- Instances

instance CoArbitrary Modality
instance Arbitrary Modality where
  arbitrary = Modality <$> arbitrary <*> arbitrary <*> arbitrary

instance CoArbitrary Q0Origin where
  coarbitrary = \case
    Q0Inferred -> variant 0
    Q0{}       -> variant 1
    Q0Erased{} -> variant 2

instance CoArbitrary Q1Origin where
  coarbitrary = \case
    Q1Inferred -> variant 0
    Q1{}       -> variant 1
    Q1Linear{} -> variant 2

instance CoArbitrary QωOrigin where
  coarbitrary = \case
    QωInferred -> variant 0
    Qω{}       -> variant 1
    QωPlenty{} -> variant 2

instance Arbitrary Q0Origin where
  arbitrary = elements [ Q0Inferred, Q0 noRange, Q0Erased noRange ]

instance Arbitrary Q1Origin where
  arbitrary = elements [ Q1Inferred, Q1 noRange, Q1Linear noRange ]

instance Arbitrary QωOrigin where
  arbitrary = elements [ QωInferred, Qω noRange, QωPlenty noRange ]

instance CoArbitrary Quantity
instance Arbitrary Quantity where
  arbitrary = elements [ Quantity0 mempty, Quantity1 mempty, Quantityω mempty ]
  -- Andreas, 2019-07-04, TODO:
  -- The monoid laws hold only modulo origin information.
  -- Thus, we generate here only origin-free quantities.
  -- arbitrary = oneof
  --   [ Quantity0 <$> arbitrary
  --   , Quantity1 <$> arbitrary
  --   , Quantityω <$> arbitrary
  --   ]

instance CoArbitrary Relevance
instance Arbitrary Relevance where
  arbitrary = elements allRelevances

instance CoArbitrary Cohesion
instance Arbitrary Cohesion where
  arbitrary = elements $ filter (/= Squash) allCohesions
  -- left division does not respect laws for Squash on the left.

instance Arbitrary NameId where
  arbitrary = elements [ NameId x y | x <- [0, 1], y <- [0, 1] ]

instance CoArbitrary NameId

instance Arbitrary Induction where
  arbitrary = elements [Inductive, CoInductive]

instance CoArbitrary Induction where
  coarbitrary Inductive   = variant 0
  coarbitrary CoInductive = variant 1

instance Arbitrary MetaId where
  arbitrary = MetaId <$> arbitrary

instance Arbitrary Hiding where
  arbitrary = elements [ Hidden, NotHidden, Instance NoOverlap, Instance YesOverlap ]

instance (Arbitrary a, Arbitrary b) => Arbitrary (ImportedName' a b) where
  arbitrary = do
    a <- arbitrary
    b <- arbitrary
    elements [ ImportedModule a, ImportedName b ]

deriving instance (Show a, Show b) => Show (Using' a b)

instance (Arbitrary a, Arbitrary b) => Arbitrary (Using' a b) where
  arbitrary = do
    xs <- arbitrary
    elements [ UseEverything, Using xs ]

------------------------------------------------------------------------------
-- Properties

-- Quantity is a POMonoid

prop_monoid_Quantity :: Property3 Quantity
prop_monoid_Quantity = isMonoid

prop_monotone_comp_Quantity :: Property3 Quantity
prop_monotone_comp_Quantity = isMonotoneComposition

-- -- | Quantities ω=ℕ, 1={1}, 0={0}  do not form a Galois connection.
--
-- Counterexample 1:  ω \ 1 ≤ 0  is true, but  1 ≤ ω · 0  is false
--   since {1} and {0} are not related.
--
-- Counterexample 2:  0 \ 1 ≤ ω  is true, but  1 ≤ 0 · ω  is false
--
-- prop_Galois_Quantity :: Prop3 Quantity
-- prop_Galois_Quantity = isGaloisConnection

-- Relevance is a LeftClosedPOMonoid

prop_monoid_Relevance :: Property3 Relevance
prop_monoid_Relevance = isMonoid

prop_monotone_comp_Relevance :: Property3 Relevance
prop_monotone_comp_Relevance = isMonotoneComposition

prop_Galois_Relevance :: Prop3 Relevance
prop_Galois_Relevance = isGaloisConnection

prop_left_identity_invcomp_Relevance :: Relevance -> Bool
prop_left_identity_invcomp_Relevance x = Relevant `inverseComposeRelevance` x == x

prop_right_absorptive_invcomp_Relevance :: Relevance -> Bool
prop_right_absorptive_invcomp_Relevance x = x `inverseComposeRelevance` Relevant == Relevant

-- Modality is a POMonoid

prop_monoid_Modality :: Property3 Modality
prop_monoid_Modality = isMonoid

prop_monotone_comp_Modality :: Property3 Modality
prop_monotone_comp_Modality = isMonotoneComposition

-- -- | The following does not hold, see prop_Galois_Quanity.
-- prop_Galois_Modality :: Prop3 Modality
-- prop_Galois_Modality = isGaloisConnection

-- ASR (2017-01-23): Commented out because 'Hiding' is *partial*
-- monoid.

-- -- | 'Hiding' is a monoid.
-- prop_monoid_Hiding :: Prop3 Hiding
-- prop_monoid_Hiding = isMonoid

-- | 'Using'' is a monoid.
prop_monoid_Using' :: Property3 (Using' Int Int)
prop_monoid_Using' = isMonoid

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
tests = testProperties "Internal.Syntax.Common" $allProperties
