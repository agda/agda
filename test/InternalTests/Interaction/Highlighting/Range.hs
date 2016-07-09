{-# LANGUAGE CPP #-}

module InternalTests.Interaction.Highlighting.Range ( tests ) where

import Agda.Interaction.Highlighting.Range
import Agda.Utils.List

#if __GLASGOW_HASKELL__ <= 708
import Control.Applicative ( (<$>) )
#endif

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
-- All tests

-- | All the properties.

tests :: IO Bool
tests = runTests "InternalTests.Interaction.Highlighting.Range"
  [ quickCheck' rangeInvariant
  , quickCheck' rangesInvariant
  , quickCheck' (rangesInvariant . rToR)
  , quickCheck' (\r1 r2 -> rangesInvariant $ r1 `minus` r2)
  , quickCheck' prop_rangesToPositions
  , quickCheck' prop_minus
  ]
