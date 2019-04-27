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
  , moduleName
  , rootNameModule
  , replaceModuleExtension
  ) where

import Prelude hiding (null)

import Control.Applicative hiding (empty)
import Control.Monad
import Control.Monad.Trans
import qualified Data.List as List
import Data.Maybe (catMaybes)
import qualified Data.Map as Map
import System.FilePath

import Agda.Syntax.Common
import Agda.Syntax.Concrete
import Agda.Syntax.Parser
import Agda.Syntax.Parser.Literate (literateExtsShortList)
import Agda.Syntax.Position

import Agda.TypeChecking.Monad.Base
import Agda.TypeChecking.Monad.Trace
import Agda.TypeChecking.Monad.Benchmark (billTo)
import qualified Agda.TypeChecking.Monad.Benchmark as Bench
import {-# SOURCE #-} Agda.TypeChecking.Monad.Options (getIncludeDirs)
import Agda.TypeChecking.Warnings (runPM)

import Agda.Utils.Except
import Agda.Utils.FileName
import Agda.Utils.Lens
import Agda.Utils.List ( stripSuffix )
import Agda.Utils.Null

import Agda.Utils.Impossible

-- | Converts an Agda file name to the corresponding interface file
-- name.

toIFile :: AbsolutePath -> AbsolutePath
toIFile = replaceModuleExtension ".agdai"

replaceModuleExtension :: String -> AbsolutePath -> AbsolutePath
replaceModuleExtension ext@('.':_) = mkAbsolute . (++ ext) .  dropAgdaExtension . filePath
replaceModuleExtension ext = replaceModuleExtension ('.':ext)

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
--   module name. The returned paths are absolute.
--
--   SIDE EFFECT:  Updates 'stModuleToSource'.
findFile' :: TopLevelModuleName -> TCM (Either FindError AbsolutePath)
findFile' m = do
    dirs         <- getIncludeDirs
    modFile      <- useTC stModuleToSource
    (r, modFile) <- liftIO $ findFile'' dirs m modFile
    stModuleToSource `setTCLens` modFile
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
      files <- fileList acceptableFileExts
      filesShortList <- fileList parseFileExtsShortList
      existingFiles <-
        liftIO $ filterM (doesFileExistCaseSensitive . filePath) files
      return $ case List.nub existingFiles of
        []     -> (Left (NotFound filesShortList), modFile)
        [file] -> (Right file, Map.insert m file modFile)
        files  -> (Left (Ambiguous existingFiles), modFile)
  where
    fileList exts = mapM absolute
                    [ filePath dir </> file
                    | dir  <- dirs
                    , file <- map (moduleNameToFileName m) exts
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
  ex <- liftIO $ doesFileExistCaseSensitive $ filePath f
  return $ if ex then Just f else Nothing

-- | Ensures that the module name matches the file name. The file
-- corresponding to the module name (according to the include path)
-- has to be the same as the given file name.

checkModuleName
  :: TopLevelModuleName
     -- ^ The name of the module.
  -> AbsolutePath
     -- ^ The file from which it was loaded.
  -> Maybe TopLevelModuleName
     -- ^ The expected name, coming from an import statement.
  -> TCM ()
checkModuleName name file mexpected =
  findFile' name >>= \case

    Left (NotFound files)  -> typeError $
      case mexpected of
        Nothing       -> ModuleNameDoesntMatchFileName name files
        Just expected -> ModuleNameUnexpected name expected

    Left (Ambiguous files) -> typeError $
      AmbiguousTopLevelModuleName name files

    Right file' -> do
      file <- liftIO $ absolute (filePath file)
      if file === file' then
        return ()
       else
        typeError $ ModuleDefinedInOtherFile name file file'

-- | Computes the module name of the top-level module in the given
-- file.
--
-- If no top-level module name is given, then an attempt is made to
-- use the file name as a module name.

-- TODO: Perhaps it makes sense to move this procedure to some other
-- module.

moduleName
  :: AbsolutePath
     -- ^ The path to the file.
  -> Module
     -- ^ The parsed module.
  -> TCM TopLevelModuleName
moduleName file parsedModule = billTo [Bench.ModuleName] $
  case moduleNameParts name of
    ["_"] -> do
      m <- runPM (parse moduleNameParser defaultName)
             `catchError` \_ ->
           typeError $ GenericError $
             "The file name " ++ show file ++
             " is invalid because it does not correspond to a valid module name."
      case m of
        Qual {} ->
          typeError $ GenericError $
            "The file name " ++ show file ++ " is invalid because " ++
            defaultName ++ " is not an unqualified module name."
        QName {} ->
          return $ TopLevelModuleName (getRange m) [defaultName]
    _ -> return name
  where
  name        = topLevelModuleName parsedModule
  defaultName = rootNameModule file

parseFileExtsShortList :: [String]
parseFileExtsShortList = [".agda"] ++ literateExtsShortList

dropAgdaExtension :: String -> String
dropAgdaExtension s = case catMaybes [ stripSuffix ext s
                                     | ext <- acceptableFileExts ] of
    [name] -> name
    _      -> __IMPOSSIBLE__

rootNameModule :: AbsolutePath -> String
rootNameModule = dropAgdaExtension . snd . splitFileName . filePath
