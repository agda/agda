------------------------------------------------------------------------
-- Ranges

module Agda.Interaction.Highlighting.Range
  ( Range(..)
  , rangeInvariant
  , overlapping
  , toList
  , getRanges
  , getRangesA
  , rToR
  , Agda.Interaction.Highlighting.Range.tests
  ) where

import Test.QuickCheck
import Data.List
import Agda.Utils.TestHelpers
import qualified Agda.Syntax.Abstract as A
import qualified Agda.Syntax.Concrete as C
import qualified Agda.Syntax.Position as P

-- | Character ranges. The first character in the file has position 1.
-- Note that the 'to' position is considered to be outside of the
-- range.
--
-- Invariant: @'from' '<=' 'to'@.

data Range = Range { from, to :: Integer }
             deriving (Eq, Ord, Show)

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

-- | Calculates a set of ranges associated with a name.
--
-- For an operator the ranges associated with the NameParts are
-- returned. Otherwise the range associated with the Name is returned.
--
-- A boolean, indicating operatorness, is also returned.

getRanges :: C.Name -> ([Range], Bool)
getRanges (C.NoName _ _) = ([], False)
getRanges (C.Name r ps)  =
  if r == P.noRange then (concatMap getR ps, True)
                    else (rToR r, False)
  where
  getR C.Hole     = []
  getR (C.Id r _) = rToR r

-- | Like 'getRanges', but for 'A.QName's. Note that the module part
-- of the name is thrown away; only the base part is used.

getRangesA :: A.QName -> ([Range], Bool)
getRangesA = getRanges . A.nameConcrete . A.qnameName

-- | Converts a 'P.Range' to a 'Range' (if the input range has
-- well-defined positions).

rToR :: P.Range -> [Range]
rToR r = case (p1, p2) of
  (P.Pn { P.posPos = pos1 }, P.Pn { P.posPos = pos2 }) ->
    [Range { from = toInteger pos1, to = toInteger pos2 }]
  _ -> []
  where
  p1 = P.rStart r
  p2 = P.rEnd r

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
