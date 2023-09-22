
-- | Ranges.

module Agda.Interaction.Highlighting.Range
  ( Range(..)
  , rangeInvariant
  , Ranges(..)
  , rangesInvariant
  , overlapping
  , overlappings
  , empty
  , rangeToPositions
  , rangesToPositions
  , rToR
  , rangeToRange
  , minus
  ) where

import Prelude hiding (null)

import Control.DeepSeq

import qualified Agda.Syntax.Position as P

import Agda.Utils.List
import Agda.Utils.Maybe
import Agda.Utils.Null

-- | Character ranges. The first character in the file has position 1.
-- Note that the 'to' position is considered to be outside of the
-- range.
--
-- Invariant: @'from' '<=' 'to'@.

data Range = Range { from, to :: !Int }
             deriving (Eq, Ord, Show)

instance Null Range where
  empty  = Range 0 0
  null r = to r <= from r

instance NFData Range where
  rnf (Range _ _) = ()

-- | The 'Range' invariant.

rangeInvariant :: Range -> Bool
rangeInvariant r = from r <= to r

-- | Zero or more consecutive and separated ranges.

newtype Ranges = Ranges [Range]
  deriving (Eq, Show, NFData)

-- | The 'Ranges' invariant.

rangesInvariant :: Ranges -> Bool
rangesInvariant (Ranges rs) = allConsecutive (\ r s -> to r < from s) rs

------------------------------------------------------------------------
-- Queries

-- | 'True' iff the ranges overlap.
--
-- The ranges are assumed to be well-formed.

overlapping :: Range -> Range -> Bool
overlapping r1 r2 = (not $ r1 `isLeftOf` r2) && (not $ r2 `isLeftOf` r1)

isLeftOf :: Range -> Range -> Bool
isLeftOf r1 r2 = to r1 <= from r2

overlappings :: Ranges -> Ranges -> Bool
-- specification: overlappings (Ranges r1s) (Ranges r2s) = or [ overlapping r1 r2 | r1 <- r1s, r2 <- r2s ]
overlappings (Ranges r1s) (Ranges r2s) =
  isNothing $ mergeStrictlyOrderedBy isLeftOf r1s r2s

------------------------------------------------------------------------
-- Conversion

-- | Converts a range to a list of positions.

rangeToPositions :: Range -> [Int]
rangeToPositions r = [from r .. to r - 1]

-- | Converts several ranges to a list of positions.

rangesToPositions :: Ranges -> [Int]
rangesToPositions (Ranges rs) = concatMap rangeToPositions rs

-- | Converts a 'P.Range' to a 'Ranges'.

rToR :: P.Range -> Ranges
rToR r = Ranges (map iToR (P.rangeIntervals r))
  where
  iToR (P.Interval { P.iStart = P.Pn { P.posPos = pos1 }
                   , P.iEnd   = P.Pn { P.posPos = pos2 }
                   }) =
    Range { from = fromIntegral pos1, to = fromIntegral pos2 }

-- | Converts a 'P.Range', seen as a continuous range, to a 'Range'.

rangeToRange :: P.Range -> Range
rangeToRange r =
  case P.rangeToInterval r of
    Nothing -> Range { from = 0, to = 0 }
    Just i  -> Range { from = fromIntegral $ P.posPos $ P.iStart i
                     , to   = fromIntegral $ P.posPos $ P.iEnd i
                     }

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
    | null y          = m (x:xs) ys
    | to x < from y   = x : m xs (y:ys)
    | to y < from x   = m (x:xs) ys
    | from x < from y = Range { from = from x, to = from y } :
                        m (Range { from = from y, to = to x } : xs) (y:ys)
    | to y < to x     = m (Range { from = to y, to = to x } : xs) ys
    | otherwise       = m xs (y:ys)
