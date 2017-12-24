{-# LANGUAGE TemplateHaskell #-}

module InternalTests.Interaction.Highlighting.Range ( tests ) where

import Agda.Interaction.Highlighting.Range
import qualified Agda.Syntax.Position as P
import Agda.Utils.List

import Data.List

import InternalTests.Helpers
import InternalTests.Syntax.Position ()

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

-- Template Haskell hack to make the following $quickCheckAll work
-- under ghc-7.8.
return [] -- KEEP!

-- | All tests as collected by 'quickCheckAll'.

tests :: IO Bool
tests = do
  putStrLn "InternalTests.Interaction.Highlighting.Range"
  $quickCheckAll
