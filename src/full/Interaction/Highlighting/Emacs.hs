-- | Function which gives precise syntax highlighting info to Emacs.

module Interaction.Highlighting.Emacs
  ( clearSyntaxInfo
  , appendSyntaxInfo
  , Interaction.Highlighting.Emacs.tests
  ) where

import Interaction.Highlighting.Precise
import Interaction.Highlighting.Range
import Prelude hiding (writeFile, appendFile)
import Utils.FileName
import Utils.String
import Utils.IO (writeFile, appendFile)
import Data.List
import Data.Char
import Data.Maybe
import Test.QuickCheck

------------------------------------------------------------------------
-- Read/show functions

-- | Converts the 'aspect' and 'otherAspects' fields to atoms readable
-- by the Emacs interface.

toAtoms :: MetaInfo -> [String]
toAtoms m = map toAtom (otherAspects m) ++ toAtoms' (aspect m)
  where
  toAtom x = map toLower (show x)

  toAtoms' Nothing               = []
  toAtoms' (Just (Name mKind op)) =
    map toAtom (maybeToList mKind) ++ opAtom
    where opAtom | op        = ["operator"]
                 | otherwise = []
  toAtoms' (Just a) = [toAtom a]

-- | Shows meta information in such a way that it can easily be read
-- by Emacs.

showMetaInfo :: (Range, MetaInfo) -> String
showMetaInfo (r, m) =
     "(annotation-annotate "
  ++ show (from r)
  ++ " "
  ++ show (to r)
  ++ " '("
  ++ concat (intersperse " " (toAtoms m))
  ++ ")"
  ++ (maybe " nil" ((" " ++) . quote) $ note m)
  ++ (maybe "" (\(f, p) -> " '(" ++ quote f ++ " . " ++ show p ++ ")")
        $ definitionSite m)
  ++ ")"

-- | Shows a file in an Emacsy fashion.

showFile :: File -> String
showFile = unlines . map showMetaInfo . compress

------------------------------------------------------------------------
-- IO

-- | Gives the syntax highlighting information file name associated
-- with the given Agda file.

infoFileName :: FilePath -> String
infoFileName path = dir ++ [slash, '.'] ++ name ++ ext ++ ".el"
  where (dir, name, ext) = splitFilePath path

-- | Clears a syntax highlighting information file.
--
-- The output file name is constructed from the given file name by
-- prepending \".\" and appending \".el\".

clearSyntaxInfo
  :: FilePath
     -- ^ The path to the file which should be highlighted
     -- (not the file which should be cleared).
  -> IO ()
clearSyntaxInfo path = writeFile (infoFileName path) ""

-- | Appends to a file with syntax highlighting information.

appendSyntaxInfo
  :: FilePath  -- ^ The path to the file which should be highlighted.
  -> File      -- ^ The syntax highlighting info which should be added.
  -> IO ()
appendSyntaxInfo path file =
  appendFile (infoFileName path) $ showFile file

------------------------------------------------------------------------
-- All tests

-- TODO: One could check that the show functions are invertible.

-- | All the properties.

tests :: IO ()
tests = do
  return ()
