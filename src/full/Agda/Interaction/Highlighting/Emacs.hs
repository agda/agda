-- | Functions which give precise syntax highlighting info to Emacs.

module Agda.Interaction.Highlighting.Emacs
  ( clearSyntaxInfo
  , writeEmacsFile
  , appendErrorToEmacsFile
  , Agda.Interaction.Highlighting.Emacs.tests
  ) where

import Agda.Interaction.Highlighting.Precise
import Agda.Interaction.Highlighting.Range
import Agda.Interaction.Highlighting.Generate
import Agda.TypeChecking.Monad (TCM, TCErr)
import Agda.Syntax.Abstract (QName)
import qualified Agda.Syntax.Position as P
import Agda.Syntax.Translation.ConcreteToAbstract (TopLevelInfo)
import Agda.TypeChecking.Errors (prettyError)
import Agda.Utils.FileName
import Agda.Utils.String
import Agda.Utils.TestHelpers

import Control.Monad.Trans
import Data.List
import Data.Char
import Data.Maybe
import qualified System.IO.UTF8 as UTF8

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

showFile :: CompressedFile -> String
showFile = unlines . map showMetaInfo

------------------------------------------------------------------------
-- IO

-- | Gives the syntax highlighting information file name associated
-- with the given Agda file.

infoFileName :: FilePath -> String
infoFileName path | null dir  = base
                  | otherwise = dir ++ slash : base
  where
  (dir, name, ext) = splitFilePath path
  base = '.' : name ++ ext ++ ".el"

-- | Clears a syntax highlighting information file.
--
-- The output file name is constructed from the given file name by
-- prepending \".\" and appending \".el\".

clearSyntaxInfo
  :: FilePath
     -- ^ The path to the file which should be highlighted
     -- (not the file which should be cleared).
  -> IO ()
clearSyntaxInfo path = UTF8.writeFile (infoFileName path) ""

-- | Appends to a file with syntax highlighting information.

appendSyntaxInfo :: HighlightingInfo -> IO ()
appendSyntaxInfo highlighting =
  UTF8.appendFile (infoFileName $ source highlighting)
                  (showFile $ info highlighting)

------------------------------------------------------------------------
-- Driver which uses the code in
-- Agda.Interaction.Highlighting.Generate to create syntax
-- highlighting files

-- | Outputs syntax highlighting information after clearing existing
-- highlighting info.

writeEmacsFile :: HighlightingInfo -> TCM ()
writeEmacsFile highlighting = do
  liftIO $ clearSyntaxInfo (source highlighting)
  liftIO $ appendSyntaxInfo highlighting

-- | Appends information about an error to the highlighting file
-- relevant for the error.

appendErrorToEmacsFile :: TCErr -> TCM ()
appendErrorToEmacsFile err = do
  let r = P.getRange err
  s <- prettyError err
  case P.rStart r of
    Nothing                                         -> return ()
    -- Errors for expressions entered using the command line sometimes
    -- have an empty file name component. This should be fixed.
    Just     (P.Pn { P.srcFile = "" })              -> return ()
    Just pos@(P.Pn { P.srcFile = f, P.posPos = p }) -> do
      liftIO $ appendSyntaxInfo $
        HighlightingInfo { source = f
                         , info   = compress $ generateErrorInfo r s
                         }

------------------------------------------------------------------------
-- All tests

-- TODO: One could check that the show functions are invertible.

-- | All the properties.

tests :: IO Bool
tests = runTests "Agda.Interaction.Highlighting.Emacs" []
