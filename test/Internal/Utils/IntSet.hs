{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE TemplateHaskell #-}

{-# OPTIONS_GHC -fno-warn-orphans -fno-warn-partial-type-signatures #-}

module Internal.Utils.IntSet ( tests ) where

import Agda.Utils.IntSet.Infinite
import Test.QuickCheck
import Data.Semigroup hiding (All)
import Data.List
import qualified Data.Set as Set
import Data.Foldable

import Internal.Helpers

instance Arbitrary IntSet where
  arbitrary = mconcat <$> listOf g
    where
      g = oneof
            [ pure empty, below <$> choose (-20, 4), above <$> choose (-4, 20)
            , (mconcat . map singleton) <$> listOf arbitrary ]
  shrink _ = []

subsetOf :: IntSet -> IntSet -> Bool
subsetOf r1 r2 = r1 <> r2 == r2

prop_member :: Integer -> IntSet -> _
prop_member x r = member x r === (singleton x `subsetOf` r)

prop_subtract_subset :: IntSet -> _
prop_subtract_subset r1 r2 = subsetOf r1 r2 === (difference r1 r2 == empty)

prop_invariant :: IntSet -> _
prop_invariant r = whenFail (print r) $ invariant r

prop_append_invariant :: IntSet -> _
prop_append_invariant r1 r2 = prop_invariant (r1 <> r2)

prop_append_commute :: IntSet -> _
prop_append_commute r1 r2 = r1 <> r2 === r2 <> r1

prop_append_assoc :: IntSet -> _
prop_append_assoc r1 r2 r3 = r1 <> (r2 <> r3) === (r1 <> r2) <> r3

prop_append_idem :: IntSet -> _
prop_append_idem r = r === r <> r

prop_subtract_invariant :: IntSet -> _
prop_subtract_invariant r1 r2 = prop_invariant (difference r1 r2)

prop_subtract_idem :: IntSet -> _
prop_subtract_idem r1 r2 =
  difference r1 r2 === difference (difference r1 r2) r2

prop_subtract_append :: IntSet -> _
prop_subtract_append r1 r2 =
  whenFail (putStrLn $ "r1 - r2 = " ++ show d) $
  r1 <> r2 === d <> r2
  where d = difference r1 r2

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
tests = testProperties "Internal.Utils.IntSet" $allProperties
