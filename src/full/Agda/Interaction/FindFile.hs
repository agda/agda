------------------------------------------------------------------------
-- | Functions which map between module names and file names.
--
-- Note that file name lookups are cached in the 'TCState'. The code
-- assumes that no Agda source files are added or removed from the
-- include directories while the code is being type checked.
------------------------------------------------------------------------

module Agda.Interaction.FindFile
  ( SourceFile(..), InterfaceFile(intFilePath)
  , toIFile, mkInterfaceFile
  , FindError(..), findErrorToTypeError
  , findFile, findFile', findFile''
  , findInterfaceFile', findInterfaceFile
  , checkModuleName
  , moduleName
  , rootNameModule
  , replaceModuleExtension
  ) where

import Prelude hiding (null)

import Control.Monad
import Control.Monad.Except
import Control.Monad.Trans
import Data.Maybe (catMaybes)
import qualified Data.Map as Map
import System.FilePath

import Agda.Interaction.Library ( findProjectRoot )

import Agda.Syntax.Concrete
import Agda.Syntax.Parser
import Agda.Syntax.Parser.Literate (literateExtsShortList)
import Agda.Syntax.Position

import Agda.Interaction.Options ( optLocalInterfaces )

import Agda.TypeChecking.Monad.Base
import Agda.TypeChecking.Monad.Benchmark (billTo)
import qualified Agda.TypeChecking.Monad.Benchmark as Bench
import Agda.TypeChecking.Monad.Options (libToTCM)
import Agda.TypeChecking.Warnings (runPM)

import Agda.Version ( version )

import Agda.Utils.Applicative ( (?$>) )
import Agda.Utils.FileName
import Agda.Utils.List  ( stripSuffix, nubOn )
import Agda.Utils.List1 ( List1, pattern (:|) )
import qualified Agda.Utils.List1 as List1
import Agda.Utils.Monad ( ifM, unlessM )
import Agda.Utils.Pretty ( prettyShow )
import Agda.Utils.Singleton

import Agda.Utils.Impossible

-- | Type aliases for source files and interface files.
--   We may only produce one of these if we know for sure that the file
--   does exist. We can always output an @AbsolutePath@ if we are not sure.

-- TODO: do not export @SourceFile@ and force users to check the
-- @AbsolutePath@ does exist.
newtype SourceFile    = SourceFile    { srcFilePath :: AbsolutePath } deriving (Eq, Ord)
newtype InterfaceFile = InterfaceFile { intFilePath :: AbsolutePath }

-- | Makes an interface file from an AbsolutePath candidate.
--   If the file does not exist, then fail by returning @Nothing@.

mkInterfaceFile
  :: AbsolutePath             -- ^ Path to the candidate interface file
  -> IO (Maybe InterfaceFile) -- ^ Interface file iff it exists
mkInterfaceFile fp = do
  ex <- doesFileExistCaseSensitive $ filePath fp
  pure (ex ?$> InterfaceFile fp)

-- | Converts an Agda file name to the corresponding interface file
--   name. Note that we do not guarantee that the file exists.

toIFile :: SourceFile -> TCM AbsolutePath
toIFile (SourceFile src) = do
  let fp = filePath src
  mroot <- ifM (optLocalInterfaces <$> commandLineOptions)
               {- then -} (pure Nothing)
               {- else -} (libToTCM $ findProjectRoot (takeDirectory fp))
  pure $ replaceModuleExtension ".agdai" $ case mroot of
    Nothing   -> src
    Just root ->
      let buildDir = root </> "_build" </> version </> "agda"
          fileName = makeRelative root fp
      in mkAbsolute $ buildDir </> fileName

replaceModuleExtension :: String -> AbsolutePath -> AbsolutePath
replaceModuleExtension ext@('.':_) = mkAbsolute . (++ ext) .  dropAgdaExtension . filePath
replaceModuleExtension ext = replaceModuleExtension ('.':ext)

-- | Errors which can arise when trying to find a source file.
--
-- Invariant: All paths are absolute.

data FindError
  = NotFound [SourceFile]
    -- ^ The file was not found. It should have had one of the given
    -- file names.
  | Ambiguous [SourceFile]
    -- ^ Several matching files were found.
    --
    -- Invariant: The list of matching files has at least two
    -- elements.

-- | Given the module name which the error applies to this function
-- converts a 'FindError' to a 'TypeError'.

findErrorToTypeError :: TopLevelModuleName -> FindError -> TypeError
findErrorToTypeError m (NotFound  files) = FileNotFound m (map srcFilePath files)
findErrorToTypeError m (Ambiguous files) =
  AmbiguousTopLevelModuleName m (map srcFilePath files)

-- | Finds the source file corresponding to a given top-level module
-- name. The returned paths are absolute.
--
-- Raises an error if the file cannot be found.

findFile :: TopLevelModuleName -> TCM SourceFile
findFile m = do
  mf <- findFile' m
  case mf of
    Left err -> typeError $ findErrorToTypeError m err
    Right f  -> return f

-- | Tries to find the source file corresponding to a given top-level
--   module name. The returned paths are absolute.
--
--   SIDE EFFECT:  Updates 'stModuleToSource'.
findFile' :: TopLevelModuleName -> TCM (Either FindError SourceFile)
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
  -> IO (Either FindError SourceFile, ModuleToSource)
findFile'' dirs m modFile =
  case Map.lookup m modFile of
    Just f  -> return (Right (SourceFile f), modFile)
    Nothing -> do
      files          <- fileList acceptableFileExts
      filesShortList <- fileList parseFileExtsShortList
      existingFiles  <-
        liftIO $ filterM (doesFileExistCaseSensitive . filePath . srcFilePath) files
      return $ case nubOn id existingFiles of
        []     -> (Left (NotFound filesShortList), modFile)
        [file] -> (Right file, Map.insert m (srcFilePath file) modFile)
        files  -> (Left (Ambiguous existingFiles), modFile)
  where
    fileList exts = mapM (fmap SourceFile . absolute)
                    [ filePath dir </> file
                    | dir  <- dirs
                    , file <- map (moduleNameToFileName m) exts
                    ]

-- | Finds the interface file corresponding to a given top-level
-- module file. The returned paths are absolute.
--
-- Raises 'Nothing' if the the interface file cannot be found.

findInterfaceFile'
  :: SourceFile                 -- ^ Path to the source file
  -> TCM (Maybe InterfaceFile)  -- ^ Maybe path to the interface file
findInterfaceFile' fp = liftIO . mkInterfaceFile =<< toIFile fp

-- | Finds the interface file corresponding to a given top-level
-- module file. The returned paths are absolute.
--
-- Raises an error if the source file cannot be found, and returns
-- 'Nothing' if the source file can be found but not the interface
-- file.

findInterfaceFile :: TopLevelModuleName -> TCM (Maybe InterfaceFile)
findInterfaceFile m = findInterfaceFile' =<< findFile m

-- | Ensures that the module name matches the file name. The file
-- corresponding to the module name (according to the include path)
-- has to be the same as the given file name.

checkModuleName
  :: TopLevelModuleName
     -- ^ The name of the module.
  -> SourceFile
     -- ^ The file from which it was loaded.
  -> Maybe TopLevelModuleName
     -- ^ The expected name, coming from an import statement.
  -> TCM ()
checkModuleName name (SourceFile file) mexpected = do
  findFile' name >>= \case

    Left (NotFound files)  -> typeError $
      case mexpected of
        Nothing -> ModuleNameDoesntMatchFileName name (map srcFilePath files)
        Just expected -> ModuleNameUnexpected name expected

    Left (Ambiguous files) -> typeError $
      AmbiguousTopLevelModuleName name (map srcFilePath files)

    Right src -> do
      let file' = srcFilePath src
      file <- liftIO $ absolute (filePath file)
      unlessM (liftIO $ sameFile file file') $
        typeError $ ModuleDefinedInOtherFile name file file'

  -- Andreas, 2020-09-28, issue #4671:  In any case, make sure
  -- that we do not end up with a mismatch between expected
  -- and actual module name.

  forM_ mexpected $ \ expected ->
    unless (name == expected) $
      typeError $ OverlappingProjects file name expected
      -- OverlappingProjects is the correct error for
      -- test/Fail/customized/NestedProjectRoots
      -- -- typeError $ ModuleNameUnexpected name expected


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
    "_" :| [] -> do
      m <- runPM (parse moduleNameParser defaultName)
             `catchError` \_ ->
           typeError $ GenericError $
             "The file name " ++ prettyShow file ++
             " is invalid because it does not correspond to a valid module name."
      case m of
        Qual {} ->
          typeError $ GenericError $
            "The file name " ++ prettyShow file ++ " is invalid because " ++
            defaultName ++ " is not an unqualified module name."
        QName {} ->
          return $ TopLevelModuleName (getRange m) $ singleton defaultName
    _ -> return name
  where
  name        = topLevelModuleName parsedModule
  defaultName = rootNameModule file

parseFileExtsShortList :: [String]
parseFileExtsShortList = ".agda" : literateExtsShortList

dropAgdaExtension :: String -> String
dropAgdaExtension s = case catMaybes [ stripSuffix ext s
                                     | ext <- acceptableFileExts ] of
    [name] -> name
    _      -> __IMPOSSIBLE__

rootNameModule :: AbsolutePath -> String
rootNameModule = dropAgdaExtension . snd . splitFileName . filePath
