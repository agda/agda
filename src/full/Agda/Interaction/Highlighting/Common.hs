-- | Common syntax highlighting functions for Emacs and JSON

module Agda.Interaction.Highlighting.Common
  ( toAtoms
  , chooseHighlightingMethod
  ) where

import Agda.Interaction.Highlighting.Precise
import Agda.Interaction.Highlighting.Range
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
  kindToAtom (Module _)                = "module"
  kindToAtom k                         = toAtom k

  toAtoms' Nothing               = []
  toAtoms' (Just (Name mKind op)) =
    map kindToAtom (maybeToList mKind) ++ opAtom
    where opAtom | op        = ["operator"]
                 | otherwise = []
  toAtoms' (Just a) = [toAtom a]

-- | Chooses which method to use.
chooseHighlightingMethod
  :: Either Ranges HighlightingInfo
     -- ^ @'Left' rs@: Remove highlighting from the ranges @rs@.
  -> HighlightingMethod
  -> HighlightingMethod
chooseHighlightingMethod info method = case (info, method) of
  (_,      Direct)       -> Direct
  (Left _, _)            -> Direct
  (Right info, Indirect) -> case toList info of
    ((_, mi) : _)
      | otherAspects mi == Set.singleton TypeChecks ||
        mi == mempty -> Direct
    _                -> Indirect
