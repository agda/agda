{-# LANGUAGE TemplateHaskell #-}

module Internal.Utils.BiMap ( tests ) where

import Agda.Utils.BiMap

import qualified Data.List as List
import qualified Data.Map as Map
import Data.Tuple ( swap )

import Internal.Helpers

------------------------------------------------------------------------
-- * Instances
------------------------------------------------------------------------

instance (Ord a, Ord b, Arbitrary a, Arbitrary b) => Arbitrary (BiMap a b) where
  arbitrary = fromList <$> do List.zip <$> alist <*> blist
    where
      alist = List.nub <$> arbitrary
      blist = List.nub <$> arbitrary

------------------------------------------------------------------------
-- * Properties
------------------------------------------------------------------------

prop_BiMap_invariant :: (Ord a, Ord b) => BiMap a b -> Bool
prop_BiMap_invariant (BiMap t u) =
  Map.toAscList t == List.sort (List.map swap (Map.toList u))

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
tests = testProperties "Internal.Utils.BiMap" $allProperties
