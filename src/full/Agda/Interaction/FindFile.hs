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
  , findFile, findFile', findFile'_, findFile''
  , findInterfaceFile', findInterfaceFile
  , checkModuleName
  , moduleName
  , rootNameModule
  , replaceModuleExtension
  ) where

import Prelude hiding (null)

import Control.Monad
import Control.Monad.Except
import Control.Monad.State
import Control.Monad.Trans
import Data.Maybe (catMaybes)
import qualified Data.Map as Map
import qualified Data.Text as T
import System.FilePath

import Agda.Interaction.Library ( findProjectRoot )

import Agda.Syntax.Concrete
import Agda.Syntax.Parser
import Agda.Syntax.Parser.Literate (literateExtsShortList)
import Agda.Syntax.Position
import Agda.Syntax.TopLevelModuleName

import Agda.Interaction.Options ( optLocalInterfaces )

import Agda.TypeChecking.Monad.Base
import Agda.TypeChecking.Monad.Benchmark (billTo)
import qualified Agda.TypeChecking.Monad.Benchmark as Bench
import {-# SOURCE #-} Agda.TypeChecking.Monad.Options
  (getIncludeDirs, libToTCM)
import Agda.TypeChecking.Monad.State ( registerFileIdWithBuiltin, topLevelModuleName )
import Agda.TypeChecking.Monad.Trace (runPM, setCurrentRange)
import Agda.TypeChecking.Warnings    (warning)

import Agda.Version ( version )

import Agda.Utils.Applicative ( (?$>) )
import Agda.Utils.CallStack   ( HasCallStack )
import Agda.Utils.FileId
import Agda.Utils.FileName
import Agda.Utils.List  ( stripSuffix, nubOn )
import Agda.Utils.List1 ( List1, pattern (:|) )
import Agda.Utils.List2 ( List2, pattern List2 )
import qualified Agda.Utils.List1 as List1
import qualified Agda.Utils.List2 as List2
import Agda.Utils.Monad ( ifM, unlessM )
import Agda.Syntax.Common.Pretty ( Pretty(..), prettyShow )
import qualified Agda.Syntax.Common.Pretty as P
import Agda.Utils.Singleton

import Agda.Utils.Impossible

-- This instance isn't producing something pretty.
-- instance Pretty SourceFile where
--   pretty = pretty . srcFileId

-- | File must exist.
newtype InterfaceFile = InterfaceFile { intFilePath :: AbsolutePath }

instance Pretty InterfaceFile where
  pretty = pretty . intFilePath

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

toIFile :: HasCallStack => SourceFile -> TCM AbsolutePath
toIFile (SourceFile fi) = do
  src <- fileFromId fi -- partial function, thus HasCallStack
  let fp = filePath src
  let localIFile = replaceModuleExtension ".agdai" src
  mroot <- libToTCM $ findProjectRoot (takeDirectory fp)
  case mroot of
    Nothing   -> pure localIFile
    Just root -> do
      let buildDir = root </> "_build" </> version </> "agda"
      fileName <- liftIO $ makeRelativeCanonical root (filePath localIFile)
      let separatedIFile = mkAbsolute $ buildDir </> fileName
          ifilePreference = ifM (optLocalInterfaces <$> commandLineOptions)
            (pure (localIFile, separatedIFile))
            (pure (separatedIFile, localIFile))
      separatedIFileExists <- liftIO $ doesFileExistCaseSensitive $ filePath separatedIFile
      localIFileExists <- liftIO $ doesFileExistCaseSensitive $ filePath localIFile
      case (separatedIFileExists, localIFileExists) of
        (False, False) -> fst <$> ifilePreference
        (False, True) -> pure localIFile
        (True, False) -> pure separatedIFile
        (True, True) -> do
          ifiles <- ifilePreference
          warning $ uncurry DuplicateInterfaceFiles ifiles
          pure $ fst ifiles

replaceModuleExtension :: String -> AbsolutePath -> AbsolutePath
replaceModuleExtension ext@('.':_) = mkAbsolute . (++ ext) .  dropAgdaExtension . filePath
replaceModuleExtension ext = replaceModuleExtension ('.':ext)

-- | Errors which can arise when trying to find a source file.
--
-- Invariant: All paths are absolute.

data FindError
  = NotFound [AbsolutePath]
      -- ^ The file was not found.
      --   It should have had one of the given file names.
  | Ambiguous (List2 AbsolutePath)
      -- ^ Several matching files were found.
  deriving Show

-- | Given the module name which the error applies to this function
-- converts a 'FindError' to a 'TypeError'.

findErrorToTypeError :: TopLevelModuleName -> FindError -> TypeError
findErrorToTypeError m = \case
  NotFound  files -> FileNotFound m files
  Ambiguous files -> AmbiguousTopLevelModuleName m files

-- findErrorToTypeError :: MonadFileId m => TopLevelModuleName -> FindError -> m TypeError
-- findErrorToTypeError m = \case
--   NotFound  files -> FileNotFound m <$> mapM srcFilePath files
--   Ambiguous files -> AmbiguousTopLevelModuleName m <$> mapM srcFilePath files

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
    dirs     <- getIncludeDirs
    modToSrc <- useTC stModuleToSource
    (r, modToSrc) <- liftIO $ runStateT (findFile'' dirs m) modToSrc
    stModuleToSource `setTCLens` modToSrc
    return r

-- | A variant of 'findFile'' which manipulates an extra 'ModuleToSourceId'

findFile'_ ::
     List1 AbsolutePath
       -- ^ Include paths.
  -> TopLevelModuleName
  -> StateT ModuleToSourceId TCM (Either FindError SourceFile)
findFile'_ incs m = do
  dict <- useTC stFileDict
  m2s  <- get
  (r, ModuleToSource dict' m2s') <- liftIO $
    runStateT (findFile'' incs m) $ ModuleToSource dict m2s
  setTCLens stFileDict dict'
  put m2s'
  return r

-- | A variant of 'findFile'' which does not require 'TCM'.

findFile'' ::
     List1 AbsolutePath
       -- ^ Include paths.
  -> TopLevelModuleName
  -> StateT ModuleToSource IO (Either FindError SourceFile)
findFile'' dirs m = do
  ModuleToSource dict modToSrc <- get
  case Map.lookup m modToSrc of
    Just sf -> return $ Right sf
    Nothing -> do
      files          <- liftIO $ fileList acceptableFileExts
      filesShortList <- liftIO $ fileList $ List2.toList parseFileExtsShortList
      existingFiles  <- liftIO $ filterM (doesFileExistCaseSensitive . filePath) files
      case nubOn id existingFiles of
        [file]   -> do
          let (i, dict') = registerFileIdWithBuiltin file dict
          let src = SourceFile i
          put $ ModuleToSource dict' $ Map.insert m src modToSrc
          return (Right src)
        []       -> return (Left (NotFound filesShortList))
        f0:f1:fs -> return (Left (Ambiguous $ List2 f0 f1 fs))
  where
    fileList exts = mapM absolute
                    [ filePath dir </> file
                    | dir  <- List1.toList dirs
                    , file <- map (moduleNameToFileName m) exts
                    ]

-- | Finds the interface file corresponding to a given top-level
-- module file. The returned paths are absolute.
--
-- Raises 'Nothing' if the interface file cannot be found.

findInterfaceFile' :: HasCallStack  -- We are calling partial function toIFile, thus want a call stack.
  => SourceFile                 -- ^ Path to the source file
  -> TCM (Maybe InterfaceFile)  -- ^ Maybe path to the interface file
findInterfaceFile' fp = liftIO . mkInterfaceFile =<< toIFile fp


-- | Finds the interface file corresponding to a given top-level
-- module file. The returned paths are absolute.
--
-- Raises an error if the source file cannot be found, and returns
-- 'Nothing' if the source file can be found but not the interface
-- file.

findInterfaceFile :: HasCallStack  -- because of calling a partial function
  => TopLevelModuleName -> TCM (Maybe InterfaceFile)
findInterfaceFile m = findInterfaceFile' =<< findFile m

-- | Ensures that the module name matches the file name. The file
-- corresponding to the module name (according to the include path)
-- has to be the same as the given file name.

checkModuleName ::
     TopLevelModuleName
       -- ^ The name of the module.
  -> SourceFile
       -- ^ The file from which it was loaded.
  -> Maybe TopLevelModuleName
       -- ^ The expected name, coming from an import statement.
  -> TCM ()
checkModuleName name src0 mexpected = do
  file <- srcFilePath src0
  findFile' name >>= \case

    Left (NotFound files)  -> typeError $
      case mexpected of
        Nothing -> ModuleNameDoesntMatchFileName name files
        Just expected -> ModuleNameUnexpected name expected

    Left (Ambiguous files) -> typeError $
      AmbiguousTopLevelModuleName name files

    Right src -> do
      file' <- srcFilePath src
      file  <- liftIO $ absolute $ filePath file
      unlessM (liftIO $ sameFile file file') $
        typeError $ ModuleDefinedInOtherFile name file file'

  -- Andreas, 2020-09-28, issue #4671:  In any case, make sure
  -- that we do not end up with a mismatch between expected
  -- and actual module name.

  forM_ mexpected \ expected ->
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
moduleName file parsedModule = billTo [Bench.ModuleName] $ do
  let defaultName = rootNameModule file
      raw         = rawTopLevelModuleNameForModule parsedModule
  topLevelModuleName =<< if isNoName raw
    then setCurrentRange (rangeFromAbsolutePath file) do
      m <- runPM (fst <$> parse moduleNameParser defaultName)
             `catchError` \_ ->
           typeError $ InvalidFileName file DoesNotCorrespondToValidModuleName
      case m of
        Qual {} ->
          typeError $ InvalidFileName file $
            RootNameModuleNotAQualifiedModuleName $ T.pack defaultName
        QName {} ->
          return $ RawTopLevelModuleName
            { rawModuleNameRange = getRange m
            , rawModuleNameParts = singleton (T.pack defaultName)
            }
    else return raw

parseFileExtsShortList :: List2 String
parseFileExtsShortList = List2.cons ".agda" literateExtsShortList

dropAgdaExtension :: String -> String
dropAgdaExtension s = case catMaybes [ stripSuffix ext s
                                     | ext <- acceptableFileExts ] of
    [name] -> name
    _      -> __IMPOSSIBLE__

rootNameModule :: AbsolutePath -> String
rootNameModule = dropAgdaExtension . snd . splitFileName . filePath
