-- | Common syntax highlighting functions for Emacs and JSON

module Agda.Interaction.Highlighting.Common
  ( toAtoms
  , chooseHighlightingMethod
  ) where

import Agda.Interaction.Options
import Agda.Interaction.Highlighting.Precise
import Agda.Syntax.Common
import Agda.TypeChecking.Monad (HighlightingMethod(..))
import Data.Maybe (maybeToList)
import Data.Char (toLower)
import qualified Data.Set as Set

-- | Converts the 'aspect' and 'otherAspects' fields to strings that are
-- friendly to editors.
toAtoms :: Aspects -> [String]
toAtoms m = map toAtom (Set.toList $ otherAspects m)
         ++ toAtoms' (aspect m)
  where

  toAtom :: Show a => a -> String
  toAtom = map toLower . show

  kindToAtom (Constructor Inductive)   = "inductiveconstructor"
  kindToAtom (Constructor CoInductive) = "coinductiveconstructor"
  kindToAtom k                         = toAtom k

  toAtoms' Nothing               = []
  toAtoms' (Just (Name mKind op)) =
    map kindToAtom (maybeToList mKind) ++ opAtom
    where opAtom | op        = ["operator"]
                 | otherwise = []
  toAtoms' (Just a) = [toAtom a]

-- | Choose which method to use based on HighlightingInfo and HighlightingMethod
chooseHighlightingMethod
  :: HighlightingInfo
  -> HighlightingMethod
  -> HighlightingMethod
chooseHighlightingMethod info method = case ranges info of
  _             | method == Direct -> Direct
  ((_, mi) : _) | check mi         -> Direct
  _                                -> Indirect

  where check mi = otherAspects mi == Set.singleton TypeChecks
                || mi == mempty
