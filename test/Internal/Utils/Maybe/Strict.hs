{-# LANGUAGE TemplateHaskell #-}

module Internal.Utils.Maybe.Strict ( tests ) where

import Agda.Utils.Maybe.Strict

import Data.Semigroup ()

import Prelude hiding ( Maybe )

import Internal.Helpers

------------------------------------------------------------------------------
-- Instances

instance Arbitrary a => Arbitrary (Maybe a) where
  arbitrary = toStrict <$> arbitrary
  shrink    = map toStrict . shrink . toLazy

instance CoArbitrary a => CoArbitrary (Maybe a) where
  coarbitrary = coarbitrary . toLazy

------------------------------------------------------------------------------
-- Properties

-- | 'Maybe a' is a monoid.
prop_monoid_Maybe :: Property3 (Maybe ())
prop_monoid_Maybe = isMonoid

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
tests = testProperties "Internal.Utils.Maybe.Strict" $allProperties
