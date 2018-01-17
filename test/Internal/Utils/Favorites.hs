{-# LANGUAGE TemplateHaskell #-}

module Internal.Utils.Favorites ( tests ) where

import Agda.Utils.Favorites
import Agda.Utils.Null
import Agda.Utils.PartialOrd
import Agda.Utils.Singleton

import Internal.Utils.PartialOrd ( ISet(ISet) )

import Prelude hiding ( null )

import Internal.Helpers

------------------------------------------------------------------------
-- * Instances
------------------------------------------------------------------------

instance (PartialOrd a, Arbitrary a) => Arbitrary (Favorites a) where
  arbitrary = fromList <$> arbitrary

------------------------------------------------------------------------
-- * Properties
------------------------------------------------------------------------

property_null_empty :: Bool
property_null_empty = null (empty :: Favorites ())

property_not_null_singleton :: forall a. a -> Bool
property_not_null_singleton x = not $ null (singleton x :: Favorites a)

-- Remember: less is better!

prop_compareWithFavorites :: ISet -> Favorites ISet -> Bool
prop_compareWithFavorites a@ISet{} as =
  case compareWithFavorites a as of
    Dominates dominated notDominated ->
      all (related a POLT) dominated &&
      all (related a POAny) notDominated
    IsDominated dominator ->
      related a POGE dominator

prop_fromList_after_toList :: Favorites ISet -> Bool
prop_fromList_after_toList as =
  fromList (toList as) == as

-- | A second way to compute the 'union' is to use 'compareFavorites'.
prop_union_union2 :: Favorites ISet -> Favorites ISet -> Bool
prop_union_union2 as bs =
  union as bs == union2 as bs
    where union2 as bs = unionCompared $ compareFavorites as bs

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
tests = testProperties "Internal.Utils.Favorites" $allProperties
