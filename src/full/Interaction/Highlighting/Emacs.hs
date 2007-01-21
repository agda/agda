-- | Function which gives precise syntax highlighting info to Emacs.

module Interaction.Highlighting.Emacs (writeSyntaxInfo) where

import Interaction.Highlighting.Precise
import Utils.FileName
import Utils.String
import Data.List
import Data.Char

-- | Shows an aspect in an Emacsy way.

showAspect :: Aspect -> String
showAspect = map toLower . show

-- | Shows a range in such a way that it can easily be read by Emacs.

showRange :: Range -> String
showRange r =
     "(annotation-annotate "
  ++ show (from r)
  ++ " "
  ++ show (to r)
  ++ " '("
  ++ concat (intersperse " " (map showAspect (aspects r)))
  ++ ")"
  ++ (maybe "" ((" " ++) . quote) $ note r)
  ++ ")"

-- | Shows a file in an Emacsy fashion.

showFile :: File -> String
showFile = unlines . map showRange

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
