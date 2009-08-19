------------------------------------------------------------------------
-- | Functions which map between module names and file names.
--
-- Note that file name lookups are cached in the 'TCState'. The code
-- assumes that no Agda source files are added or removed from the
-- include directories while the code is being type checked.
------------------------------------------------------------------------

module Agda.Interaction.FindFile
  ( toIFile
  , FindError(..), findErrorToTypeError
  , findFile, findFile', findFile''
  , findInterfaceFile
  , checkModuleName
  , ModuleToSource
  , SourceToModule, sourceToModule
  , tests
  ) where

import Control.Applicative
import Control.Monad
import Control.Monad.State.Class
import Control.Monad.Trans
import Data.List
import Data.Map (Map)
import qualified Data.Map as Map
import System.FilePath
import System.Directory

import Agda.Syntax.Concrete.Name
import Agda.TypeChecking.Monad
import Agda.Utils.FileName
import Agda.Utils.Monad

-- | Converts an Agda file name to the corresponding interface file
-- name.

toIFile :: AbsolutePath -> AbsolutePath
toIFile f = mkAbsolute (replaceExtension (filePath f) ".agdai")

-- | Errors which can arise when trying to find a source file.
--
-- Invariant: All paths are absolute.

data FindError
  = NotFound [AbsolutePath]
    -- ^ The file was not found. It should have had one of the given
    -- file names.
  | Ambiguous [AbsolutePath]
    -- ^ Several matching files were found.
    --
    -- Invariant: The list of matching files has at least two
    -- elements.

-- | Given the module name which the error applies to this function
-- converts a 'FindError' to a 'TypeError'.

findErrorToTypeError :: TopLevelModuleName -> FindError -> TypeError
findErrorToTypeError m (NotFound  files) = FileNotFound m files
findErrorToTypeError m (Ambiguous files) =
  AmbiguousTopLevelModuleName m files

-- | Finds the source file corresponding to a given top-level module
-- name. The returned paths are absolute.
--
-- Raises an error if the file cannot be found.

findFile :: TopLevelModuleName -> TCM AbsolutePath
findFile m = do
  mf <- findFile' m
  case mf of
    Left err -> typeError $ findErrorToTypeError m err
    Right f  -> return f

-- | Tries to find the source file corresponding to a given top-level
-- module name. The returned paths are absolute.

findFile' :: TopLevelModuleName -> TCM (Either FindError AbsolutePath)
findFile' m = do
    dirs         <- getIncludeDirs
    modFile      <- stModuleToSource <$> get
    (r, modFile) <- liftIO $ findFile'' dirs m modFile
    modify $ \s -> s { stModuleToSource = modFile }
    return r

-- | A variant of 'findFile'' which does not require 'TCM'.

findFile''
  :: [AbsolutePath]
  -- ^ Include paths.
  -> TopLevelModuleName
  -> ModuleToSource
  -- ^ Cached invocations of 'findFile'''. An updated copy is returned.
  -> IO (Either FindError AbsolutePath, ModuleToSource)
findFile'' dirs m modFile =
    case Map.lookup m modFile of
      Just f  -> return (Right f, modFile)
      Nothing -> do
        existingFiles <-
          liftIO $ filterM (doesFileExist . filePath) files
        return $ case nub existingFiles of
          []     -> (Left (NotFound files), modFile)
          [file] -> (Right file, Map.insert m file modFile)
          files  -> (Left (Ambiguous files), modFile)
    where
    files = [ mkAbsolute (filePath dir </> file)
            | dir  <- dirs
            , file <- map (moduleNameToFileName m) [".agda", ".lagda"]
            ]

-- | Finds the interface file corresponding to a given top-level
-- module name. The returned paths are absolute.
--
-- Raises an error if the source file cannot be found, and returns
-- 'Nothing' if the source file can be found but not the interface
-- file.

findInterfaceFile :: TopLevelModuleName -> TCM (Maybe AbsolutePath)
findInterfaceFile m = do
  f  <- toIFile <$> findFile m
  ex <- liftIO $ doesFileExist $ filePath f
  return $ if ex then Just f else Nothing

-- | Ensures that the module name matches the file name. The file
-- corresponding to the module name (according to the include path)
-- has to be the same as the given file name.

checkModuleName :: TopLevelModuleName
                   -- ^ The name of the module.
                -> AbsolutePath
                   -- ^ The file from which it was loaded.
                -> TCM ()
checkModuleName name file = do
  moduleShouldBeIn <- findFile' name
  case moduleShouldBeIn of
    Left (NotFound files)  -> typeError $
                                ModuleNameDoesntMatchFileName name files
    Left (Ambiguous files) -> typeError $
                                AmbiguousTopLevelModuleName name files
    Right file' ->
      ifM (liftIO $ filePath file === filePath file')
          (return ())
          (typeError $ ModuleDefinedInOtherFile name file file')

-- | Maps top-level module names to the corresponding source file
-- names.

type ModuleToSource = Map TopLevelModuleName AbsolutePath

-- | Maps source file names to the corresponding top-level module
-- names.

type SourceToModule = Map AbsolutePath TopLevelModuleName

-- | Creates a 'SourceToModule' map based on 'stModuleToSource'.

sourceToModule :: TCM SourceToModule
sourceToModule =
  Map.fromList
     .  map (\(m, f) -> (f, m))
     .  Map.toList
     .  stModuleToSource
    <$> get
