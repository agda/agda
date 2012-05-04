{-# LANGUAGE DeriveDataTypeable #-}

-- | Ranges.

module Agda.Interaction.Highlighting.Range
  ( Range(..)
  , rangeInvariant
  , Ranges(..)
  , rangesInvariant
  , overlapping
  , empty
  , rangeToPositions
  , rangesToPositions
  , rToR
  , minus
  , Agda.Interaction.Highlighting.Range.tests
  ) where

import Control.Applicative ((<$>))
import Data.List
import Data.Typeable (Typeable)

import qualified Agda.Syntax.Position as P
import Agda.Utils.List
import Agda.Utils.TestHelpers
import Agda.Utils.QuickCheck

-- | Character ranges. The first character in the file has position 1.
-- Note that the 'to' position is considered to be outside of the
-- range.
--
-- Invariant: @'from' '<=' 'to'@.

data Range = Range { from, to :: Integer }
             deriving (Eq, Ord, Show, Typeable)

-- | The 'Range' invariant.

rangeInvariant :: Range -> Bool
rangeInvariant r = from r <= to r

-- | Zero or more consecutive and separated ranges.

newtype Ranges = Ranges [Range]
  deriving (Eq, Show)

-- | The 'Ranges' invariant.

rangesInvariant :: Ranges -> Bool
rangesInvariant (Ranges []) = True
rangesInvariant (Ranges rs) =
  and (zipWith (<) (map to $ init rs) (map from $ tail rs))

------------------------------------------------------------------------
-- Queries

-- | 'True' iff the ranges overlap.
--
-- The ranges are assumed to be well-formed.

overlapping :: Range -> Range -> Bool
overlapping r1 r2 = not $
  to r1 <= from r2 || to r2 <= from r1

-- | 'True' iff the range is empty.

empty :: Range -> Bool
empty r = to r <= from r

------------------------------------------------------------------------
-- Conversion

-- | Converts a range to a list of positions.

rangeToPositions :: Range -> [Integer]
rangeToPositions r = [from r .. to r - 1]

-- | Converts several ranges to a list of positions.

rangesToPositions :: Ranges -> [Integer]
rangesToPositions (Ranges rs) = concatMap rangeToPositions rs

prop_rangesToPositions rs = sorted (rangesToPositions rs)

-- | Converts a 'P.Range' to a 'Ranges'.

rToR :: P.Range -> Ranges
rToR (P.Range is) = Ranges (map iToR is)
  where
  iToR (P.Interval { P.iStart = P.Pn { P.posPos = pos1 }
                   , P.iEnd   = P.Pn { P.posPos = pos2 }
                   }) =
    Range { from = toInteger pos1, to = toInteger pos2 }

------------------------------------------------------------------------
-- Operations

-- | @minus xs ys@ computes the difference between @xs@ and @ys@: the
-- result contains those positions which are present in @xs@ but not
-- in @ys@.
--
-- Linear in the lengths of the input ranges.

minus :: Ranges -> Ranges -> Ranges
minus (Ranges rs1) (Ranges rs2) = Ranges (m rs1 rs2)
  where
  m []     _      = []
  m xs     []     = xs
  m (x:xs) (y:ys)
    | empty y         = m (x:xs) ys
    | to x < from y   = x : m xs (y:ys)
    | to y < from x   = m (x:xs) ys
    | from x < from y = Range { from = from x, to = from y } :
                        m (Range { from = from y, to = to x } : xs) (y:ys)
    | to y < to x     = m (Range { from = to y, to = to x } : xs) ys
    | otherwise       = m xs (y:ys)

prop_minus xs ys =
  rangesToPositions (xs `minus` ys) ==
  rangesToPositions xs \\ rangesToPositions ys

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
-- All tests

-- | All the properties.

tests :: IO Bool
tests = runTests "Agda.Interaction.Highlighting.Range"
  [ quickCheck' rangeInvariant
  , quickCheck' rangesInvariant
  , quickCheck' (rangesInvariant . rToR)
  , quickCheck' (\r1 r2 -> rangesInvariant $ r1 `minus` r2)
  , quickCheck' prop_rangesToPositions
  , quickCheck' prop_minus
  ]
