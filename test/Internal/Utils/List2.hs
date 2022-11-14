{-# LANGUAGE TemplateHaskell #-}

module Internal.Utils.List2 ( tests ) where

import Data.Maybe

import Agda.Utils.List  (uncons)
import Agda.Utils.List1 (List1)
import Agda.Utils.List2 as List2

import Internal.Helpers

instance Arbitrary a => Arbitrary (List2 a) where
  arbitrary = List2 <$> arbitrary <*> arbitrary <*> arbitrary
  shrink (List2 x y ys) = concat $
    [ -- drop x
      [ List2 y z zs | (z,zs) <- maybeToList $ uncons ys ]
    , -- drop y
      [ List2 x z zs | (z,zs) <- maybeToList $ uncons ys ]
    , -- drop from ys
      map (List2 x y) $ shrink ys
    ]

instance CoArbitrary a => CoArbitrary (List2 a) where
  coarbitrary (List2 x y zs) = coarbitrary (x, y, zs)

------------------------------------------------------------------------
-- * Properties
------------------------------------------------------------------------

prop_iso_List1Either_1 :: Either Int (List2 Int) -> Bool
prop_iso_List1Either_1 e = fromList1Either (toList1Either e) == e

prop_iso_List1Either_2 :: List1 Int -> Bool
prop_iso_List1Either_2 xs = toList1Either (fromList1Either xs) == xs

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
tests = testProperties "Internal.Utils.List2" $allProperties
