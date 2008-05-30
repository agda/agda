-- | Functions which give precise syntax highlighting info to Emacs.

module Agda.Interaction.Highlighting.Emacs
  ( clearSyntaxInfo
  , appendSyntaxInfo
  , generateEmacsFile
  , generateAndOutputSyntaxInfo
  , generateAndOutputTerminationProblemInfo
  , Agda.Interaction.Highlighting.Emacs.tests
  ) where

import Agda.Interaction.Highlighting.Precise
import Agda.Interaction.Highlighting.Range
import Agda.Interaction.Highlighting.Generate
import Agda.Interaction.Options
import Agda.TypeChecking.Monad hiding (MetaInfo)
import Agda.Syntax.Abstract hiding (Name)
import Agda.Syntax.Translation.ConcreteToAbstract
import Agda.Syntax.Parser
import Prelude hiding (writeFile, appendFile)
import Agda.Utils.IO (writeFile, appendFile)
import Agda.Utils.FileName
import Agda.Utils.Monad
import Agda.Utils.String
import Control.Monad.Trans
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
clearSyntaxInfo path = writeFile (infoFileName path) ""

-- | Appends to a file with syntax highlighting information.

appendSyntaxInfo
  :: FilePath  -- ^ The path to the file which should be highlighted.
  -> File      -- ^ The syntax highlighting info which should be added.
  -> IO ()
appendSyntaxInfo path file =
  appendFile (infoFileName path) $ showFile file

------------------------------------------------------------------------
-- Drivers which use the code in Agda.Interaction.Highlighting.Generate to
-- create syntax highlighting files

-- | Generates highlighting information for syntax and termination
-- issues. Assumes that type checking has been done.

generateEmacsFile
  :: FilePath           -- ^ The module to highlight.
  -> TopLevelInfo       -- ^ The abstract syntax of the module.
  -> [([QName], [Range])]
     -- ^ Function definitions which do not pass the termination
     -- checker (grouped if they are mutual), and corresponding
     -- problematic call sites.
  -> TCM ()
generateEmacsFile file topLevel errs = do
  liftIO $ clearSyntaxInfo file
  ignoreAbstractMode $ do
    generateAndOutputSyntaxInfo file TypeCheckingDone topLevel
    generateAndOutputTerminationProblemInfo file errs

-- | Generates and outputs syntax highlighting information.
--
-- (Does not clear existing highlighting info, use 'clearSyntaxInfo'
-- for that.)

generateAndOutputSyntaxInfo
  :: FilePath           -- ^ The module to highlight.
  -> TypeCheckingState  -- ^ Has it been type checked?
  -> TopLevelInfo       -- ^ The abstract syntax of the module.
  -> TCM ()
generateAndOutputSyntaxInfo file tcs topLevel = do
  tokens <- liftIO $ parseFile' tokensParser file
  syntaxInfo <- generateSyntaxInfo tcs tokens topLevel
  liftIO $ appendSyntaxInfo file syntaxInfo

-- | Generates and outputs termination checking information.
--
-- (Does not clear existing highlighting info, use 'clearSyntaxInfo'
-- for that.)

generateAndOutputTerminationProblemInfo
  :: FilePath
     -- ^ The module to highlight.
  -> [([QName], [Range])]
     -- ^ Problematic function definitions (grouped if they are
     -- mutual), and corresponding problematic call sites.
  -> TCM ()
generateAndOutputTerminationProblemInfo file errs = do
  termInfo <- generateTerminationInfo errs
  liftIO $ appendSyntaxInfo file termInfo

------------------------------------------------------------------------
-- All tests

-- TODO: One could check that the show functions are invertible.

-- | All the properties.

tests :: IO ()
tests = do
  return ()
