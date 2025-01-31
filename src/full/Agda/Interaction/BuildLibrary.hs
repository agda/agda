-- | Type-check all files of a library (option @--build-library@).

module Agda.Interaction.BuildLibrary (buildLibrary) where

import           Control.Monad.Except             (throwError)
import           Control.Monad.IO.Class           (liftIO)

import           Data.Functor                     (void)
import qualified Data.Set as Set

import           System.Directory                 (getCurrentDirectory)
import           System.FilePath                  ( (</>) )
import qualified System.FilePath.Find             as Find

import           Agda.Interaction.FindFile        (hasAgdaExtension, checkModuleName)
import qualified Agda.Interaction.Imports         as Imp
import           Agda.Interaction.Library         (pattern AgdaLibFile, _libIncludes, getAgdaLibFile)
import           Agda.Interaction.Options         (optOnlyScopeChecking)

import           Agda.TypeChecking.Monad
import           Agda.TypeChecking.Pretty         (prettyTCM, text, vsep)
import           Agda.TypeChecking.Pretty.Warning (getAllWarnings)
import           Agda.TypeChecking.Warnings       (pattern AllWarnings, classifyWarnings)

import           Agda.Utils.FileName              (absolute)
import           Agda.Utils.Functor               ()
import           Agda.Utils.IO.Directory          (findWithInfo)
import           Agda.Utils.Monad                 (forM, forM_, unless, bracket_)
import           Agda.Utils.Null                  (unlessNullM)
import           Agda.Utils.String                (delimiter)

import           Agda.Utils.Impossible            (__IMPOSSIBLE__)

-- | Find @.agda-lib@ file from current directory
--   and build all modules located in the @include@ paths
--   and their subdirectories of the library.
--
buildLibrary :: TCM ()
buildLibrary = do
  cwd <- liftIO getCurrentDirectory

  -- Read the library file.
  ls <- libToTCM $ getAgdaLibFile cwd
  libFile@AgdaLibFile{ _libIncludes = paths } <- case ls of
    [l] -> pure l
    []  -> throwError $ GenericException "No library found to build"
    _   -> __IMPOSSIBLE__

  -- Find all modules in the include paths of the library.
  files <- map Find.infoPath . concat <$> forM paths \ path -> do
    liftIO $ findWithInfo (pure True) (hasAgdaExtension <$> Find.filePath) path

  -- Call the type-checker on all these modules.
  -- (Code copied from Agda.Main.)

  opts <- commandLineOptions
  let mode = if optOnlyScopeChecking opts
             then Imp.ScopeCheck
             else Imp.TypeCheck

  forM_ files \ inputFile -> do

    -- TODO: isolated check
    -- typeCheckMain does not isolate
    sf <- srcFromPath =<< liftIO (absolute inputFile)
    src <- Imp.parseSource sf
    let m = Imp.srcModuleName src
    -- checkModuleName m (Imp.srcOrigin src) Nothing
    -- void $ Imp.getNonMainInterface m (Just src)
    -- Preserve/restore the current pragma options, which will be mutated when loading
    -- and checking the interface.
    result <- bracket_ (useTC stPragmaOptions) (stPragmaOptions `setTCLens`) $
      Imp.typeCheckMain mode src

    -- unless (Imp.crMode result == ModuleScopeChecked) $
    --   Imp.raiseNonFatalErrors result

    -- let i = crInterface result
    -- reportSDoc "main" 50 $ pretty i
    return ()

  -- Print accumulated warnings
  unlessNullM (tcWarnings . classifyWarnings . Set.toAscList <$> getAllWarnings AllWarnings) $ \ ws -> do
    let banner = text $ "\n" ++ delimiter "All done; warnings encountered"
    alwaysReportSDoc "warning" 1 $
      vsep $ (banner :) $ map prettyTCM $ Set.toAscList ws
