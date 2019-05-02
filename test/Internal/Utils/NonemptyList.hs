{-# LANGUAGE TemplateHaskell #-}

module Internal.Utils.NonemptyList ( tests ) where

import Data.Maybe

import Internal.Helpers

import Agda.Utils.NonemptyList

import Agda.Utils.Impossible

------------------------------------------------------------------------
-- * Instances
------------------------------------------------------------------------

instance Arbitrary a => Arbitrary (NonemptyList a) where
  arbitrary = fromMaybe __IMPOSSIBLE__ . fromList . getNonEmpty <$> arbitrary
  shrink = map (fromMaybe __IMPOSSIBLE__ . fromList . getNonEmpty) . shrink . (NonEmpty . toList)

------------------------------------------------------------------------
-- * Properties
------------------------------------------------------------------------

prop_NonemptyList_roundtrip :: Eq a => NonemptyList a -> Bool
prop_NonemptyList_roundtrip l = maybe False (l ==) $ fromList $ toList l

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
