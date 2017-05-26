{-# LANGUAGE CPP             #-}
{-# LANGUAGE TemplateHaskell #-}

module InternalTests.Syntax.Common ( tests ) where

import Agda.Syntax.Common

#if __GLASGOW_HASKELL__ <= 708
import Control.Applicative ( (<$>) )
#endif

import InternalTests.Helpers

------------------------------------------------------------------------------
-- Instances

instance Arbitrary Relevance where
  arbitrary = elements allRelevances

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

-- ASR (2017-01-23): Commented out because 'Hiding' is *partial*
-- monoid.

-- | 'Hiding' is a monoid.
-- prop_monoid_Hiding :: Hiding -> Hiding -> Hiding -> Bool
-- prop_monoid_Hiding = isMonoid

-- | 'Using'' is a monoid.
prop_monoid_Using' :: Using' Int Int -> Using' Int Int -> Using' Int Int ->
                      Bool
prop_monoid_Using' = isMonoid

------------------------------------------------------------------------
-- Hack to make $quickCheckAll work under ghc-7.8
return []

-- All tests
tests :: IO Bool
tests = do
  putStrLn "InternalTests.Syntax.Common"
  $quickCheckAll
