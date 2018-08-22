-- | Common syntax highlighting functions for Emacs and JSON

module Agda.Interaction.Highlighting.Common
  ( toAtoms
  , chooseHighlightingMethod
  ) where

import Agda.Interaction.Highlighting.Precise
import Agda.Syntax.Common
import Agda.TypeChecking.Monad (HighlightingMethod(..))
import Data.Maybe (maybeToList)
import Data.Char (toLower)

-- | Converts the 'aspect' and 'otherAspects' fields to strings that are
-- friendly to editors.
toAtoms :: Aspects -> [String]
toAtoms m = map toAtom (otherAspects m) ++ toAtoms' (aspect m)
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
  _             | method == Direct                   -> Direct
  ((_, mi) : _) | otherAspects mi == [TypeChecks] ||
                  mi == mempty                       -> Direct
  _                                                  -> Indirect
