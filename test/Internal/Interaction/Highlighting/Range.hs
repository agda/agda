{-# LANGUAGE TemplateHaskell #-}

module Internal.Interaction.Highlighting.Range ( tests ) where

import Agda.Interaction.Highlighting.Range
import qualified Agda.Syntax.Position as P
import Agda.Utils.List

import Data.List

import Internal.Helpers
import Internal.Syntax.Position ()

------------------------------------------------------------------------
-- Generators

instance Arbitrary Range where
  arbitrary = do
    [from, to] <- fmap sort $ vectorOf 2 positive
    return $ Range { from = from, to = to }

instance CoArbitrary Range where
  coarbitrary (Range f t) = coarbitrary f . coarbitrary t

instance Arbitrary Ranges where
  arbitrary = rToR <$> arbitrary

------------------------------------------------------------------------
-- Range and ranges

prop_rangeInvariant :: Range -> Bool
prop_rangeInvariant = rangeInvariant

prop_rangesInvariant1 :: Ranges -> Bool
prop_rangesInvariant1 = rangesInvariant

prop_rangesInvariant2 :: P.Range -> Bool
prop_rangesInvariant2 = rangesInvariant . rToR

prop_rangesInvariant3 :: Ranges -> Ranges -> Bool
prop_rangesInvariant3 r1 r2 = rangesInvariant $ r1 `minus` r2

prop_overlappings :: Ranges -> Ranges -> Bool
prop_overlappings rs1 rs2 = overlappings rs1 rs2 == overlappings_spec rs1 rs2
  where
    overlappings_spec (Ranges r1s) (Ranges r2s) = or [ overlapping r1 r2 | r1 <- r1s, r2 <- r2s ]

------------------------------------------------------------------------
-- Conversion

prop_rangesToPositions :: Ranges -> Bool
prop_rangesToPositions rs = sorted (rangesToPositions rs)

------------------------------------------------------------------------
-- Operations

prop_minus :: Ranges -> Ranges -> Bool
prop_minus xs ys =
  rangesToPositions (xs `minus` ys) ==
  rangesToPositions xs \\ rangesToPositions ys

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
tests = testProperties "Internal.Interaction.Highlighting.Range" $allProperties
