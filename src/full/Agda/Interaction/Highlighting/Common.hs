-- | Common syntax highlighting functions for Emacs and JSON

module Agda.Interaction.Highlighting.Common
  ( toAtoms
  , chooseHighlightingMethod
  , writeToTempFile
  ) where

import Agda.Interaction.Highlighting.Precise
import Agda.Syntax.Common
import Agda.TypeChecking.Monad (HighlightingMethod(..))
import qualified Agda.Utils.IO.UTF8 as UTF8

import qualified Control.Exception as E
import Data.Maybe (maybeToList)
import Data.Char (toLower)
import qualified System.Directory as D
import qualified System.IO as IO

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

-- | Creates a temporary file, writes some stuff, and returns the filepath
writeToTempFile :: String -> IO FilePath
writeToTempFile content = do
  dir      <- D.getTemporaryDirectory
  filepath <- E.bracket (IO.openTempFile dir "agda2-mode") (IO.hClose . snd) $ \ (filepath, handle) -> do
    UTF8.hPutStr handle content
    return filepath
  return filepath

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
