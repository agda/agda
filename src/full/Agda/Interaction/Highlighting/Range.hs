{-# LANGUAGE DeriveDataTypeable #-}

-- | Ranges.

module Agda.Interaction.Highlighting.Range
  ( Range(..)
  , rangeInvariant
  , overlapping
  , toList
  , rToR
  , Agda.Interaction.Highlighting.Range.tests
  ) where

import Agda.Utils.QuickCheck
import Data.List
import Data.Generics (Typeable, Data)
import Agda.Utils.TestHelpers
import qualified Agda.Syntax.Position as P

-- | Character ranges. The first character in the file has position 1.
-- Note that the 'to' position is considered to be outside of the
-- range.
--
-- Invariant: @'from' '<=' 'to'@.

data Range = Range { from, to :: Integer }
             deriving (Eq, Ord, Show, Typeable, Data)

-- | The 'Range' invariant.

rangeInvariant :: Range -> Bool
rangeInvariant r = from r <= to r

-- | 'True' iff the ranges overlap.
--
-- The ranges are assumed to be well-formed.

overlapping :: Range -> Range -> Bool
overlapping r1 r2 = not $
  to r1 <= from r2 || to r2 <= from r1

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
  ]
