{-# LANGUAGE CPP             #-}
{-# LANGUAGE TemplateHaskell #-}

module InternalTests.Utils.BiMap ( tests ) where

import Agda.Utils.BiMap

#if __GLASGOW_HASKELL__ <= 708
import Control.Applicative ( (<$>), (<*>) )
#endif

import qualified Data.List as List
import qualified Data.Map as Map
import Data.Tuple ( swap )

import Test.QuickCheck

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

-- Template Haskell hack to make the following $quickCheckAll work
-- under ghc-7.8.
return [] -- KEEP!

tests :: IO Bool
tests = do
  putStrLn "InternalTests.Utils.BiMap"
  $quickCheckAll
