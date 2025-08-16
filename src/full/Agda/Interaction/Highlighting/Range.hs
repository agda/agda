{-# OPTIONS_GHC -Wunused-imports #-}
{-# OPTIONS_GHC -Wunused-matches #-}
{-# OPTIONS_GHC -Wunused-binds #-}

-- | Converting generic ranges to Agda's ranges.

module Agda.Interaction.Highlighting.Range
  ( module Agda.Utils.Range
  , rToR
  , rangeToRange
  ) where

import Agda.Syntax.Position qualified as P
import Agda.Utils.Range

-- | Converts a 'P.Range' to a 'Ranges'.

rToR :: P.Range -> Ranges
rToR r = Ranges (map iToR (P.rangeIntervals r))
  where
  iToR (P.Interval () P.Pn'{ P.posPos = pos1 } P.Pn'{ P.posPos = pos2 }) =
    Range { from = fromIntegral pos1, to = fromIntegral pos2 }

-- | Converts a 'P.Range', seen as a continuous range, to a 'Range'.

rangeToRange :: P.Range -> Range
rangeToRange r =
  case P.rangeToInterval r of
    Nothing -> Range { from = 0, to = 0 }
    Just (P.Interval _ s e) -> Range
      { from = fromIntegral $ P.posPos s
      , to   = fromIntegral $ P.posPos e
      }
