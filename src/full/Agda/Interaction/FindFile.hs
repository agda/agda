------------------------------------------------------------------------
-- | Functions which map between module names and file names.
--
-- Note that file name lookups are cached in the 'TCState'. The code
-- assumes that no Agda source files are added or removed from the
-- include directories while the code is being type checked.
------------------------------------------------------------------------

module Agda.Interaction.FindFile
  ( toIFile
  , findFile, findFile', findFile''
  , findInterfaceFile
  , checkModuleName
  , ModuleToSource
  , SourceToModule, sourceToModule
  ) where

import Control.Applicative
import Control.Monad
import Control.Monad.State.Class
import Control.Monad.Trans
import Data.Map (Map)
import qualified Data.Map as Map
import System.FilePath
import System.Directory

import Agda.Syntax.Concrete.Name
import Agda.TypeChecking.Monad
import Agda.Utils.FileName

-- | Converts an Agda file name to the corresponding interface file
-- name.

toIFile :: FilePath -> FilePath
toIFile f = replaceExtension f ".agdai"

-- | Finds the source file corresponding to a given top-level module
-- name. The returned paths are absolute.
--
-- Raises an error if the file cannot be found.

findFile :: TopLevelModuleName -> TCM FilePath
findFile m = do
  mf <- findFile' m
  case mf of
    Left files -> typeError $ FileNotFound m files
    Right f    -> return f

-- | Finds the source file corresponding to a given top-level module
-- name. The returned paths are absolute.
--
-- Returns @'Left' files@ if the file cannot be found, where @files@
-- is the list of files which the module could have been defined in.

findFile' :: TopLevelModuleName -> TCM (Either [FilePath] FilePath)
findFile' m = do
    dirs         <- getIncludeDirs
    modFile      <- stModuleToSource <$> get
    (r, modFile) <- liftIO $ findFile'' dirs m modFile
    modify $ \s -> s { stModuleToSource = modFile }
    return r

-- | A variant of 'findFile'' which does not require 'TCM'.

findFile''
  :: [FilePath]
  -- ^ Include paths.
  -> TopLevelModuleName
  -> ModuleToSource
  -- ^ Cached invocations of 'findFile'''. An updated copy is returned.
  -> IO (Either [FilePath] FilePath, ModuleToSource)
findFile'' dirs m modFile =
    case Map.lookup m modFile of
      Just f  -> return (Right f, modFile)
      Nothing -> do
        files' <- liftIO $ nubFiles =<< filterM doesFileExist files
        case files' of
          []       -> return (Left files, modFile)
          file : _ -> return (Right file, Map.insert m file modFile)
    where
    files = [ dir </> file
            | dir  <- dirs
            , file <- map (moduleNameToFileName m) [".agda", ".lagda"]
            ]

-- | Finds the interface file corresponding to a given top-level
-- module name. The returned paths are absolute.
--
-- Raises an error if the source file cannot be found, and returns
-- 'Nothing' if the source file can be found but not the interface
-- file.

findInterfaceFile :: TopLevelModuleName -> TCM (Maybe FilePath)
findInterfaceFile m = do
  f  <- toIFile <$> findFile m
  ex <- liftIO $ doesFileExist f
  return $ if ex then Just f else Nothing

-- | Ensures that the module name matches the file name. The file
-- corresponding to the module name (according to the include path)
-- has to be the same as the given file name.

checkModuleName :: TopLevelModuleName
                   -- ^ The name of the module.
                -> FilePath
                   -- ^ The file from which it was loaded.
                -> TCM ()
checkModuleName name file = do
  moduleShouldBeIn <- findFile' name
  case moduleShouldBeIn of
    Left files  -> typeError $
                     ModuleNameDoesntMatchFileName name files
    Right file' -> if file' == file then
                     return ()
                    else
                     typeError $
                       ModuleDefinedInOtherFile name file file'

-- | Maps top-level module names to the corresponding source file
-- names.

type ModuleToSource = Map TopLevelModuleName FilePath

-- | Maps source file names to the corresponding top-level module
-- names.

type SourceToModule = Map FilePath TopLevelModuleName

-- | Creates a 'SourceToModule' map based on 'stModuleToSource'.

sourceToModule :: TCM SourceToModule
sourceToModule =
  Map.fromList
     .  map (\(m, f) -> (f, m))
     .  Map.toList
     .  stModuleToSource
    <$> get
