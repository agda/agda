
module Agda.Interaction.Highlighting.LaTeX.Backend
  ( generateLaTeX
  ) where

import Agda.Interaction.Highlighting.LaTeX.Base
  ( LaTeXOptions(..)
  , LogLaTeXT
  , runLogLaTeXTWith
  , logMsgToText
  , generateLaTeXIO
  , prepareCommonAssets
  )

import qualified Data.Map as Map
import qualified Data.Text as T

import System.FilePath ( (</>) )

import Agda.Interaction.Options
  ( CommandLineOptions
    ( optGenerateLaTeX
    , optLaTeXDir
    , optInputFile
    , optPragmaOptions
    , optGHCiInteraction
    )
  , PragmaOptions( optCountClusters )
  )

import Agda.Syntax.Abstract.Name (toTopLevelModuleName)
import Agda.Syntax.Concrete.Name (TopLevelModuleName, projectRoot)

import Agda.TypeChecking.Monad
  ( HasOptions(commandLineOptions)
  , Interface(iModuleName)
  , TCM
  , MonadDebug
  , stModuleToSource
  , useTC
  , ReadTCState
  , reportS
  )

import Agda.Utils.FileName (filePath, mkAbsolute)

------------------------------------------------------------------------
-- * Main.

-- Command-line flag options, prior to e.g. path resolution and validation.
data LaTeXFlags = LaTeXFlags
  { latexFlagOutDir        :: FilePath
  , latexFlagSourceFile    :: Maybe FilePath
  , latexFlagGenerateLaTeX :: Bool
    -- ^ Are we going to try to generate LaTeX at all?
  } deriving Eq

-- | Generates a LaTeX file for the given interface.
--
-- The underlying source file is assumed to match the interface, but
-- this is not checked. TODO: Fix this problem, perhaps by storing the
-- source code in the interface.
generateLaTeX :: Interface -> TCM ()
generateLaTeX i = do
  let moduleName = toTopLevelModuleName $ iModuleName i
  latexFlags <- laTeXFlagsFromCommandLineOpts <$> commandLineOptions
  latexOpts <- resolveLaTeXOptions latexFlags moduleName
  runLogLaTeXWithMonadDebug $ do
    prepareCommonAssets (latexOptOutDir latexOpts)
    generateLaTeXIO latexOpts i

runLogLaTeXWithMonadDebug :: MonadDebug m => LogLaTeXT m a -> m a
runLogLaTeXWithMonadDebug = runLogLaTeXTWith $ (reportS "compile.latex" 1) . T.unpack . logMsgToText

-- Extract the LaTeX-specific command line options from the global ones.
laTeXFlagsFromCommandLineOpts :: CommandLineOptions -> LaTeXFlags
laTeXFlagsFromCommandLineOpts opts = LaTeXFlags
  { latexFlagOutDir        = optLaTeXDir opts
  , latexFlagSourceFile    = optInputFile opts
  , latexFlagGenerateLaTeX = optGenerateLaTeX opts
  }

-- Resolve the raw flags into usable LaTeX options.
resolveLaTeXOptions :: (HasOptions m, ReadTCState m) => LaTeXFlags -> TopLevelModuleName -> m LaTeXOptions
resolveLaTeXOptions flags moduleName = do
  options <- commandLineOptions
  modFiles <- useTC stModuleToSource
  let
    mSrcFileName = (mkAbsolute . filePath) <$> Map.lookup moduleName modFiles
    countClusters = optCountClusters . optPragmaOptions $ options
    latexDir = latexFlagOutDir flags
    -- FIXME: This reliance on emacs-mode to decide whether to interpret the output location as project-relative or
    -- cwd-relative is gross. Also it currently behaves differently for JSON mode :-/
    -- And it prevents us from doing a real "one-time" setup.
    outDir = case (mSrcFileName, optGHCiInteraction options) of
      (Just sourceFile, True) -> filePath (projectRoot sourceFile moduleName) </> latexDir
      _ -> latexDir
  return LaTeXOptions
    { latexOptOutDir         = outDir
    , latexOptSourceFileName = mSrcFileName
    , latexOptCountClusters  = countClusters
    }
