-- | Function which gives precise syntax highlighting info to Emacs.

module Interaction.Highlighting.Emacs
  ( writeSyntaxInfo
  , Interaction.Highlighting.Emacs.tests
  ) where

import Interaction.Highlighting.Precise
import Utils.FileName
import Utils.String
import Data.List
import Data.Char
import Test.QuickCheck

------------------------------------------------------------------------
-- Read/show functions

-- | Converts the 'aspect' and 'dotted' fields to atoms readable by
-- the Emacs interface.

toAtoms :: MetaInfo -> [String]
toAtoms m = dottedAtom ++ toAtoms' (aspect m)
  where
  toAtom x = map toLower (show x)

  dottedAtom | dotted m  = ["dotted"]
             | otherwise = []

  toAtoms' Nothing               = []
  toAtoms' (Just (Name kind op)) = [toAtom kind] ++ opAtom
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

-- | Outputs a file with syntax highlighting information.
--
-- The output file name is constructed from the given file name by
-- prepending \".\" and appending \".el\".

writeSyntaxInfo
  :: FilePath  -- ^ The path to the file which should be highlighted.
  -> File      -- ^ The syntax highlighting info for the file.
  -> IO ()
writeSyntaxInfo path file = writeFile infoFile $ showFile file
  where
  (dir, name, ext) = splitFilePath path
  infoFile = dir ++ [slash, '.'] ++ name ++ ext ++ ".el"

------------------------------------------------------------------------
-- All tests

-- TODO: One could check that the show functions are invertible.

-- | All the properties.

tests :: IO ()
tests = do
  return ()
