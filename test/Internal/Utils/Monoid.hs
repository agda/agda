{-# LANGUAGE TemplateHaskell #-}

module Internal.Utils.Monoid ( tests ) where

import Agda.Utils.Monoid

import Internal.Helpers

------------------------------------------------------------------------
-- Instances

instance Arbitrary MaxNat where
  arbitrary = do
    NonNegative x <- arbitrary :: Gen (NonNegative Int)
    return (MaxNat x)

------------------------------------------------------------------------------
-- Properties

-- | 'MaxNat' is a monoid.
prop_monoid_MaxNat :: Property3 MaxNat
prop_monoid_MaxNat = isMonoid

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
tests = testProperties "Internal.Utils.Monoid" $allProperties
