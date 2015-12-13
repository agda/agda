{-# LANGUAGE CPP #-}
------------------------------------------------------------------------
-- | Functions which map between module names and file names.
--
-- Note that file name lookups are cached in the 'TCState'. The code
-- assumes that no Agda source files are added or removed from the
-- include directories while the code is being type checked.
------------------------------------------------------------------------

module Agda.Interaction.FindFile
  ( toIFile, toIFile'
  , FindError(..), findErrorToTypeError
  , findFile, findFile', findFile''
  , findInterfaceFile
  , checkModuleName
  , moduleName', moduleName
  , tests
  ) where

import Control.Applicative
import Control.Monad
import Control.Monad.Trans
import Data.List
import qualified Data.Map as Map
import System.FilePath
import Data.Maybe

import Agda.Syntax.Concrete
import Agda.Syntax.Parser
import Agda.TypeChecking.Monad.Base
import Agda.TypeChecking.Monad.Imports
import Agda.TypeChecking.Monad.Benchmark (billTo)
import qualified Agda.TypeChecking.Monad.Benchmark as Bench
import {-# SOURCE #-} Agda.TypeChecking.Monad.Options (getIncludeDirs, commandLineOptions)
import Agda.Interaction.Options (optInterfaceDir)
import Agda.Utils.Except
import Agda.Utils.FileName
import Agda.Utils.Lens
import Agda.Packaging.Base as PKGS
import Agda.Packaging.Database

#include "undefined.h"
import Agda.Utils.Impossible


-- | Errors which can arise when trying to find a source file.
--
-- Invariant: All paths are absolute.


data FindError
  = NotFound [AbsolutePath]
    -- ^ The file was not found. It should have had one of the given
    -- file names.
  | Ambiguous [ModulePath]
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

-- | Converts an Agda file name to the corresponding interface file
-- name.
toIFile :: TopLevelModuleName -> AbsolutePath -> TCM AbsolutePath
toIFile m f = asAbsolutePath =<< toIFile' m (PlainPath f)

toIFile' :: TopLevelModuleName -> ModulePath -> TCM ModulePath
toIFile' _ (InPackage p f) = return $ InPackage p $ replaceExtension f ".agdai"
toIFile' m (PlainPath f) = do
  idir <- optInterfaceDir <$> commandLineOptions
  PlainPath <$>
    case idir of
      Just d -> liftIO $ absolute $ d </> moduleNameToFileName m ".agdai"
      Nothing -> return $ mkAbsolute (replaceExtension (filePath f) ".agdai")

-- | Finds the source file corresponding to a given top-level module
-- name. The returned paths are absolute.
--
-- Raises an error if the file cannot be found.

findFile :: TopLevelModuleName -> TCM ModulePath
findFile m = do
  mf <- findFile' m
  case mf of
    Left err -> typeError $ findErrorToTypeError m err
    Right f  -> return f

-- | Tries to find the source file corresponding to a given top-level
--   module name. The returned paths are absolute.
--
--   SIDE EFFECT:  Updates 'stModuleToSource'.
findFile' :: TopLevelModuleName -> TCM (Either FindError ModulePath)
findFile' m = do
    dirs         <- getIncludeDirs
    dbs          <- getPackageDBs
    modFile      <- use stModuleToSource
    (r, modFile) <- liftIO $ findFile'' dbs dirs m modFile
    stModuleToSource .= modFile
    return r

-- | A variant of 'findFile'' which does not require 'TCM'.

findFile''
  :: PkgDBStack
  -> [AbsolutePath]
  -- ^ Include paths.
  -> TopLevelModuleName
  -> ModuleToSource
  -- ^ Cached invocations of 'findFile'''. An updated copy is returned.
  -> IO (Either FindError ModulePath, ModuleToSource)
findFile'' dbs dirs m modFile =
  case Map.lookup m modFile of
    Just f  -> return (Right f, modFile)
    Nothing -> do
      files <- mapM (liftIO . absolute)
                    [ filePath dir </> file
                    | dir  <- dirs
                    , file <- map (moduleNameToFileName m)
                                  [".agda", ".lagda"]
                    ]
      existingFiles <- (++)
        <$> (map PlainPath <$> (liftIO $ filterM (doesFileExistCaseSensitive . filePath) files))
        <*> PKGS.findSrc' dbs m
      return $ case nub existingFiles of
        []     -> (Left (NotFound files), modFile)
        [file] -> (Right file, Map.insert m file modFile)
        files  -> (Left (Ambiguous files), modFile)

-- | Finds the interface file corresponding to a given top-level
-- module name. The returned paths are absolute.
--
-- Raises an error if the source file cannot be found, and returns
-- 'Nothing' if the source file can be found but not the interface
-- file.

findInterfaceFile :: TopLevelModuleName -> TCM (Maybe ModulePath)
findInterfaceFile m = do
  f  <- toIFile' m =<< findFile m
  case f of
    PlainPath f -> do
      ex <- liftIO $ doesFileExistCaseSensitive $ filePath f
      return $ if ex then Just (PlainPath f) else Nothing
    InPackage _ _ -> return $ Just f

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
    Right (PlainPath file') -> do
      file <- liftIO $ absolute (filePath file)
      if file === file' then
        return ()
       else
        typeError $ ModuleDefinedInOtherFile name file file'
    Right (InPackage _ _) -> return () -- Has already been checked at package build time.

-- | Computes the module name of the top-level module in the given file.
--
--   Warning! Parses the whole file to get the module name out.
--   Use wisely!

moduleName' :: AbsolutePath -> TCM TopLevelModuleName
moduleName' file = billTo [Bench.ModuleName] $ do
  name <- topLevelModuleName <$> liftIO (parseFile' moduleParser file)
  case name of
    TopLevelModuleName ["_"] -> do
      _ <- liftIO (parse moduleNameParser defaultName)
             `catchError` \_ ->
           typeError $
             GenericError $ "Invalid file name: " ++ show file ++ "."
      return $ TopLevelModuleName [defaultName]
    _ -> return name
  where
    defaultName = rootName file

-- | A variant of 'moduleName'' which raises an error if the file name
-- does not match the module name.
--
-- The file name is interpreted relative to the current working
-- directory (unless it is absolute).

moduleName :: AbsolutePath -> TCM TopLevelModuleName
moduleName file = do
  m <- moduleName' file
  checkModuleName m file
  return m
