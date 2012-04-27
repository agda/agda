{-# LANGUAGE DeriveDataTypeable #-}

-- | Ranges.

module Agda.Interaction.Highlighting.Range
  ( Range(..)
  , rangeInvariant
  , overlapping
  , empty
  , toList
  , rToR
  , minus
  , bounds
  , Agda.Interaction.Highlighting.Range.tests
  ) where

import Agda.Utils.QuickCheck
import Data.List
import Data.Typeable (Typeable)
import Agda.Utils.TestHelpers
import qualified Agda.Syntax.Position as P

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

-- | 'True' iff the ranges overlap.
--
-- The ranges are assumed to be well-formed.

overlapping :: Range -> Range -> Bool
overlapping r1 r2 = not $
  to r1 <= from r2 || to r2 <= from r1

-- | 'True' iff the range is empty.

empty :: Range -> Bool
empty r = to r <= from r

-- | Converts a range to a list of positions.

toList :: Range -> [Integer]
toList r = [from r .. to r - 1]

------------------------------------------------------------------------
-- Conversion

-- | Converts a 'P.Range' to a list of 'Range's.

rToR :: P.Range -> [Range]
rToR (P.Range is) = map iToR is
  where
  iToR (P.Interval { P.iStart = P.Pn { P.posPos = pos1 }
                   , P.iEnd   = P.Pn { P.posPos = pos2 }
                   }) =
    Range { from = toInteger pos1, to = toInteger pos2 }

-- | @minus xs ys@ takes the difference of the lists of ranges
-- @xs@ and @ys@.
-- @xs@ and @ys@ have to be sorted lists of non-adjacent ranges.
-- Linear in the length of the input ranges
minus :: [Range] -> [Range] -> [Range]
minus []     _      = []
minus xs     []     = xs
minus (x:xs) (y:ys)
    | to x < from y = x : minus xs (y:ys)
    | to y < from x = minus (x:xs) ys
    | from x < from y = Range { from = from x, to = from y} :
                            minus
                              (Range { from = from y, to = to x} : xs)
                              (y:ys)
    | to y < to x = minus
                      (Range { from = to y, to = to x} : xs)
                      ys
    | otherwise = minus xs (y:ys)

prop_minus xs ys = f zs' == f xs' \\ f ys'
  where
  xs' = rToR xs
  ys' = rToR ys
  zs' = minus xs' ys'
  f = concatMap toList

-- | Get the inclusive bounds of a non-emtpy list of ranges.

bounds :: [Range] -> (Integer,Integer)
bounds rs = (min,max-1)
  where
  min = minimum $ map from rs
  max = maximum $ map to rs

------------------------------------------------------------------------
-- Generators

instance Arbitrary Range where
  arbitrary = do
    [from, to] <- fmap sort $ vectorOf 2 positive
    return $ Range { from = from, to = to }

instance CoArbitrary Range where
  coarbitrary (Range f t) = coarbitrary f . coarbitrary t

------------------------------------------------------------------------
-- All tests

-- | All the properties.

tests :: IO Bool
tests = runTests "Agda.Interaction.Highlighting.Range"
  [ quickCheck' rangeInvariant
  , quickCheck' prop_minus
  ]
