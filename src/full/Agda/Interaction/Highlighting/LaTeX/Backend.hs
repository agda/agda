{-# OPTIONS_GHC -Wunused-imports #-}

module Agda.Interaction.Highlighting.LaTeX.Backend
  ( latexBackend
  ) where

import Agda.Interaction.Highlighting.LaTeX.Base
  ( LaTeXOptions(..)
  , MonadLogLaTeX(logLaTeX)
  , logMsgToText
  , generateLaTeXIO
  , prepareCommonAssets
  )

import Control.DeepSeq
import Control.Monad.Trans (MonadIO)

import           Data.Functor ( (<&>) )
import qualified Data.Map     as Map
import           Data.Map     ( Map )
import qualified Data.Text    as T

import GHC.Generics (Generic)

import System.FilePath ( (</>) )

import Agda.Compiler.Backend (Backend,Backend_boot(..), Backend',Backend'_boot(..), Definition, Recompile(..))
import Agda.Compiler.Common (curIF, IsMain(IsMain, NotMain))

import Agda.Interaction.Options
  ( ArgDescr(NoArg, ReqArg)
  , CommandLineOptions ( optGHCiInteraction, optPragmaOptions )
  , optCountClusters
  , Flag
  , OptDescr(..)
  )

import Agda.Syntax.Position (mkRangeFile, rangeFilePath)
import Agda.Syntax.TopLevelModuleName (TopLevelModuleName, projectRoot)

import Agda.TypeChecking.Monad
  ( HasOptions(commandLineOptions)
  , MonadDebug
  , stModuleToSourceId
  , useTC
  , ReadTCState
  , reportS
  , MonadFileId
  , srcFilePath
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
  } deriving (Eq, Generic)

instance NFData LaTeXFlags

-- | The default output directory for LaTeX.

defaultLaTeXDir :: FilePath
defaultLaTeXDir = "latex"

defaultLaTeXFlags :: LaTeXFlags
defaultLaTeXFlags = LaTeXFlags
  { latexFlagOutDir        = defaultLaTeXDir
  , latexFlagSourceFile    = Nothing
  , latexFlagGenerateLaTeX = False
  }

latexFlagsDescriptions :: [OptDescr (Flag LaTeXFlags)]
latexFlagsDescriptions =
  [ Option []     ["latex"] (NoArg latexFlag)
                  "generate LaTeX with highlighted source code"
  , Option []     ["latex-dir"] (ReqArg latexDirFlag "DIR")
                  ("directory in which LaTeX files are placed (default: " ++
                    defaultLaTeXDir ++ ")")
  ]

latexFlag :: Flag LaTeXFlags
latexFlag o = return $ o { latexFlagGenerateLaTeX = True }

latexDirFlag :: FilePath -> Flag LaTeXFlags
latexDirFlag d o = return $ o { latexFlagOutDir = d }

data LaTeXCompileEnv = LaTeXCompileEnv LaTeXFlags
data LaTeXModuleEnv  = LaTeXModuleEnv LaTeXOptions
data LaTeXModule     = LaTeXModule
data LaTeXDef        = LaTeXDef

latexBackend :: Backend
latexBackend = Backend latexBackend'

latexBackend' :: Backend' LaTeXFlags LaTeXCompileEnv LaTeXModuleEnv LaTeXModule LaTeXDef
latexBackend' = Backend'
  { backendName           = "LaTeX"
  , backendVersion        = Nothing
  , options               = defaultLaTeXFlags
  , commandLineFlags      = latexFlagsDescriptions
  , isEnabled             = latexFlagGenerateLaTeX
  , preCompile            = preCompileLaTeX
  , preModule             = preModuleLaTeX
  , compileDef            = compileDefLaTeX
  , postModule            = postModuleLaTeX
  , postCompile           = postCompileLaTeX
  , scopeCheckingSuffices = True
  , mayEraseType          = const $ return False
  , backendInteractTop    = Nothing
  , backendInteractHole   = Nothing
  }

-- | A wrapper to implement 'MonadLogLaTeX'.
newtype LogLaTeXDebugT m a = LogLaTeXDebugT { runLogLaTeXDebugT :: m a }
  deriving (Functor, Applicative, Monad, MonadIO)

instance MonadDebug m => MonadLogLaTeX (LogLaTeXDebugT m) where
  logLaTeX = LogLaTeXDebugT . (reportS "compile.latex" 1) . T.unpack . logMsgToText

-- Resolve the raw flags into usable LaTeX options.
resolveLaTeXOptions :: (HasOptions m, ReadTCState m, MonadFileId m)
  => LaTeXFlags
  -> TopLevelModuleName
  -> m LaTeXOptions
resolveLaTeXOptions flags moduleName = do
  options <- commandLineOptions
  modFiles <- useTC stModuleToSourceId
  let msrc = Map.lookup moduleName modFiles
  mf <- traverse srcFilePath msrc
  let
    mSrcFileName = mf <&> \ f ->
      mkRangeFile (mkAbsolute (filePath f)) (Just moduleName)
      -- TODO:    ^^^^^^^^^^^^^^^^^^^^^^^^^ can this just be `f`?
    countClusters = optCountClusters . optPragmaOptions $ options
    latexDir = latexFlagOutDir flags
    -- FIXME: This reliance on emacs-mode to decide whether to interpret the output location as project-relative or
    -- cwd-relative is gross. Also it currently behaves differently for JSON mode :-/
    -- And it prevents us from doing a real "one-time" setup.
    outDir = case (mSrcFileName, optGHCiInteraction options) of
      (Just sourceFile, True) ->
        filePath (projectRoot (rangeFilePath sourceFile) moduleName) </>
        latexDir
      _ -> latexDir
  return LaTeXOptions
    { latexOptOutDir         = outDir
    , latexOptSourceFileName = mSrcFileName
    , latexOptCountClusters  = countClusters
    }

preCompileLaTeX
  :: Applicative m
  => LaTeXFlags
  -> m LaTeXCompileEnv
preCompileLaTeX flags = pure $ LaTeXCompileEnv flags

preModuleLaTeX
  :: (HasOptions m, ReadTCState m, MonadFileId m)
  => LaTeXCompileEnv
  -> IsMain
  -> TopLevelModuleName
  -> Maybe FilePath
  -> m (Recompile LaTeXModuleEnv LaTeXModule)
preModuleLaTeX (LaTeXCompileEnv flags) isMain moduleName _ifacePath = case isMain of
  IsMain  -> Recompile . LaTeXModuleEnv <$> resolveLaTeXOptions flags moduleName
  NotMain -> return $ Skip LaTeXModule

compileDefLaTeX
  :: Applicative m
  => LaTeXCompileEnv
  -> LaTeXModuleEnv
  -> IsMain
  -> Definition
  -> m LaTeXDef
compileDefLaTeX _cenv _menv _main _def = pure LaTeXDef

postModuleLaTeX
  :: (MonadDebug m, ReadTCState m, MonadIO m)
  => LaTeXCompileEnv
  -> LaTeXModuleEnv
  -> IsMain
  -> TopLevelModuleName
  -> [LaTeXDef]
  -> m LaTeXModule
postModuleLaTeX _cenv (LaTeXModuleEnv latexOpts) _main _moduleName _defs = do
  i <- curIF
  runLogLaTeXDebugT do
    -- FIXME: It would be better to do "prepareCommonAssets" in @preCompileLaTeX@, but because
    -- the output directory depends on the module-relative project root (when in emacs-mode),
    -- we can't do that until we see the module.
    -- However, for now that is OK because we only generate LaTeX for the main module.
    prepareCommonAssets (latexOptOutDir latexOpts)
    generateLaTeXIO latexOpts i
  return LaTeXModule

postCompileLaTeX
  :: Applicative m
  => LaTeXCompileEnv
  -> IsMain
  -> Map TopLevelModuleName LaTeXModule
  -> m ()
postCompileLaTeX _cenv _main _modulesByName = pure ()
