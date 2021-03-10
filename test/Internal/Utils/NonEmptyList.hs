{-# LANGUAGE TemplateHaskell #-}

module Internal.Utils.NonEmptyList ( tests ) where

import Data.List.NonEmpty (NonEmpty(..), nonEmpty)
import qualified Data.List.NonEmpty as NonEmpty
import Data.Maybe

import Internal.Helpers

import Agda.Utils.Impossible

------------------------------------------------------------------------
-- * Instances
------------------------------------------------------------------------

instance Arbitrary a => Arbitrary (NonEmpty a) where
  arbitrary = fromMaybe __IMPOSSIBLE__ . nonEmpty . getNonEmpty <$> arbitrary
  shrink = map (fromMaybe __IMPOSSIBLE__ . nonEmpty . getNonEmpty) . shrink . (NonEmpty . NonEmpty.toList)

------------------------------------------------------------------------
-- * Properties
------------------------------------------------------------------------

prop_NonemptyList_roundtrip :: Eq a => NonEmpty a -> Bool
prop_NonemptyList_roundtrip l = maybe False (l ==) $ nonEmpty $ NonEmpty.toList l

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
tests = testProperties "Internal.Utils.NonemptyList" $allProperties
