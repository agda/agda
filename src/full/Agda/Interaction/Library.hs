{-# LANGUAGE OverloadedLists #-}
{-# OPTIONS_GHC -Wunused-imports #-}

-- | Library management.
--
--   Sample use:
--
--   @
--     -- Get libraries as listed in @.agda/libraries@ file.
--     libs <- getInstalledLibraries Nothing
--
--     -- Get the libraries (and immediate paths) relevant for @projectRoot@.
--     -- This involves locating and processing the @.agda-lib@ file for the project.
--     (libNames, includePaths) <-  getDefaultLibraries projectRoot True
--
--     -- Get include paths of depended-on libraries.
--     resolvedPaths <- libraryIncludePaths Nothing libs libNames
--
--     let allPaths = includePaths ++ resolvedPaths
--   @
--
module Agda.Interaction.Library
  ( findProjectRoot
  , getDefaultLibraries
  , getInstalledLibraries
  , getTrustedExecutables
  , libraryIncludePaths
  , getAgdaLibFile
  , getPrimitiveLibDir
  , classifyBuiltinModule_
  , builtinModules
  , builtinModulesWithSafePostulates
  , builtinModulesWithUnsafePostulates
  , primitiveModules
  , LibName, parseLibName
  , OptionsPragma(..)
  , AgdaLibFile(..)
  , ExeName
  , LibM
  , mkLibM
  , LibWarning(..)
  , LibPositionInfo(..)
  , libraryWarningName
  , ProjectConfig(..)
  -- * Exported for testing
  , findLib'
  ) where

import qualified Control.Exception as E
import Control.Monad.Except   ( runExceptT, MonadError, throwError )
import Control.Monad.Writer   ( Writer, runWriterT, tell )
import Control.Monad.IO.Class ( MonadIO(..) )

import Data.Bifunctor ( second )
import Data.Either
import Data.Function (on)
import qualified Data.List as List
import Data.Map ( Map )
import qualified Data.Map as Map
import Data.Set ( Set )
import qualified Data.Set as Set
import qualified Data.Text as T

import System.Directory
import System.FilePath
import System.IO.Error ( isPermissionError )

import Agda.Interaction.Library.Base
import Agda.Interaction.Library.Parse

import Agda.TypeChecking.Monad.Base.Types ( IsBuiltinModule(..) )

import Agda.Utils.Environment
import Agda.Utils.FileName
import Agda.Utils.IO ( catchIO )
import qualified Agda.Utils.IO.UTF8 as UTF8
import Agda.Utils.Lens
import Agda.Utils.List
import Agda.Utils.List1             ( List1, pattern (:|) )
import Agda.Utils.List2             ( pattern List2 )
import qualified Agda.Utils.List1   as List1
import qualified Agda.Utils.List2   as List2
import Agda.Utils.Maybe
import Agda.Utils.Monad
import Agda.Utils.Singleton
import Agda.Utils.Tuple ( mapSndM )

import Agda.Setup ( getDataFileName, getAgdaAppDir )
import Agda.Version

------------------------------------------------------------------------
-- * Types and Monads
------------------------------------------------------------------------

-- | Raise collected 'LibErrors' as exception.
--
mkLibM :: [AgdaLibFile] -> LibErrorIO a -> LibM a
mkLibM libs m = do
  (x, ews) <- lift $ lift $ runWriterT m
  let (errs, warns) = partitionEithers ews
  tell warns
  () <- List1.unlessNull errs \ errs -> throwError $ LibErrors libs errs
  return x

------------------------------------------------------------------------
-- * Resources
------------------------------------------------------------------------

-- | Returns the absolute default lib dir. This directory is used to
-- store the Primitive.agda file.
getPrimitiveLibDir :: IO AbsolutePath
getPrimitiveLibDir = do
  libdir <- filePath <$> (absolute =<< getDataFileName "lib")
  ifM (doesDirectoryExist libdir)
      (return $ AbsolutePath $ T.pack $ libdir </> "prim")
      (error $ "The lib directory " ++ libdir ++ " does not exist")

-- | The @~/.agda/libraries@ file lists the libraries Agda should know about.
--   The content of @libraries@ is a list of paths to @.agda-lib@ files.
--
--   Agda honors also version-specific @libraries@ files, e.g. @libraries-2.6.0@.
--
--   @defaultLibraryFiles@ gives a list of all @libraries@ files Agda should process
--   by default.  The first file in this list that exists is actually used.
--
defaultLibraryFiles :: List1 FilePath
defaultLibraryFiles = ("libraries-" ++ version) :| "libraries" : []

-- | The @defaultsFile@ contains a list of library names relevant for each Agda project.
--
defaultsFile :: FilePath
defaultsFile = "defaults"

-- | The @~/.agda/executables@ file lists the executables Agda should know about.
--   The content of @executables@ is a list of paths to executables.
--
--   Agda honors also version-specific @executables@ files, e.g. @executables-2.6.0@.
--
--   @defaultExecutablesFiles@ gives a list of all @executables@ Agda should process
--   by default.  The first file in this list that exists is actually used.
--
defaultExecutableFiles :: List1 FilePath
defaultExecutableFiles = ("executables-" ++ version) :| "executables" : []

------------------------------------------------------------------------
-- * Agda builtin modules
------------------------------------------------------------------------

-- | Prefix path with @Agda.Builtin@.

agdaBuiltin :: FilePath -> FilePath
agdaBuiltin = ("Agda" </>) . ("Builtin" </>)

-- | The very magical, auto-imported modules.

primitiveModules :: Set FilePath
primitiveModules = Set.fromList
  [ "Agda" </> "Primitive.agda"
  , "Agda" </> "Primitive" </> "Cubical.agda"
  ]

-- | These builtins may use postulates, and are still considered @--safe@.

builtinModulesWithSafePostulates :: Set FilePath
builtinModulesWithSafePostulates =
  (primitiveModules `Set.union`) $ Set.fromList $
  map agdaBuiltin $
    [ "Bool.agda"
    , "Char.agda"
    , "Char" </> "Properties.agda"
    , "Coinduction.agda"
    , "Cubical" </> "Equiv.agda"
    , "Cubical" </> "Glue.agda"
    , "Cubical" </> "HCompU.agda"
    , "Cubical" </> "Id.agda"
    , "Cubical" </> "Path.agda"
    , "Cubical" </> "Sub.agda"
    , "Equality" </> "Erase.agda"
    , "Equality.agda"
    , "Float.agda"
    , "Float" </> "Properties.agda"
    , "FromNat.agda"
    , "FromNeg.agda"
    , "FromString.agda"
    , "Int.agda"
    , "IO.agda"
    , "List.agda"
    , "Maybe.agda"
    , "Nat.agda"
    , "Reflection.agda"
    , "Reflection" </> "Properties.agda"
    , "Reflection" </> "External.agda"
    , "Sigma.agda"
    , "Size.agda"
    , "Strict.agda"
    , "String.agda"
    , "String" </> "Properties.agda"
    , "Unit.agda"
    , "Word.agda"
    , "Word" </> "Properties.agda"
    ]

-- | These builtins may not use postulates under @--safe@. They are not
--   automatically unsafe, but will be if they use an unsafe feature.

builtinModulesWithUnsafePostulates :: Set FilePath
builtinModulesWithUnsafePostulates = Set.fromList $
  map agdaBuiltin $
    [ "TrustMe.agda"
    , "Equality" </> "Rewrite.agda"
    ]

-- | All builtin modules.

builtinModules :: Set FilePath
builtinModules = builtinModulesWithSafePostulates `Set.union`
                 builtinModulesWithUnsafePostulates

-- | Determine whether the second absolute path refers to one of Agda's primitive modules.
--   The first argument should be the result of 'getPrimitiveLibDir'.
--
classifyBuiltinModule_ :: AbsolutePath -> AbsolutePath -> Maybe IsBuiltinModule
classifyBuiltinModule_ primLibDir fp = do
  f <- relativizeAbsolutePath fp primLibDir
  guard $ f `Set.member` builtinModules
  if f `Set.member` builtinModulesWithUnsafePostulates then return IsBuiltinModule
  else if f `Set.member` primitiveModules then return IsPrimitiveModule
  else return IsBuiltinModuleWithSafePostulates

------------------------------------------------------------------------
-- * Get the libraries for the current project
------------------------------------------------------------------------

-- | Find project root by looking for @.agda-lib@ files.
--
--   If there are none, look in the parent directories until one is found.

findProjectConfig ::
     FilePath
       -- ^ Candidate (initially: the directory Agda was called in).
  -> LibM ProjectConfig
       -- ^ Actual root and @.agda-lib@ file for this project.
findProjectConfig root = do
  getCachedProjectConfig root >>= \case
    Just conf -> return conf
    Nothing   -> handlePermissionException do
      libFiles <- liftIO $ getDirectoryContents root >>=
        filterM (\file -> and2M
          (pure $ takeExtension file == ".agda-lib")
          (doesFileExist (root </> file)))
      case libFiles of
        []     -> liftIO (upPath root) >>= \case
          Just up -> do
            conf <- over lensConfigAbove (+ 1) <$> findProjectConfig up
            storeCachedProjectConfig root conf
            return conf
          Nothing -> return DefaultProjectConfig
        [file] -> do
          let conf = ProjectConfig root file 0
          storeCachedProjectConfig root conf
          return conf
        f1:f2:files -> throwError $ LibErrors [] $ singleton $ LibError Nothing $
          SeveralAgdaLibFiles root $ List2 f1 f2 files

  where
    -- Andreas, 2024-06-26, issue #7331:
    -- In case of missing permission we terminate our search for the project file
    -- with the default value.
    handlePermissionException :: LibM ProjectConfig -> LibM ProjectConfig
    handlePermissionException = flip catchIO \ e ->
      if isPermissionError e then return DefaultProjectConfig else liftIO $ E.throwIO e

    -- Note that "going up" one directory is OS dependent
    -- if the directory is a symlink.
    --
    -- Quoting from https://hackage.haskell.org/package/directory-1.3.6.1/docs/System-Directory.html#v:canonicalizePath :
    --
    --   Note that on Windows parent directories .. are always fully
    --   expanded before the symbolic links, as consistent with the
    --   rest of the Windows API (such as GetFullPathName). In
    --   contrast, on POSIX systems parent directories .. are
    --   expanded alongside symbolic links from left to right. To
    --   put this more concretely: if L is a symbolic link for R/P,
    --   then on Windows L\.. refers to ., whereas on other
    --   operating systems L/.. refers to R.
    upPath :: FilePath -> IO (Maybe FilePath)
    upPath root = do
      up <- canonicalizePath $ root </> ".."
      if up == root then return Nothing else return $ Just up


-- | Get project root

findProjectRoot :: FilePath -> LibM (Maybe FilePath)
findProjectRoot root = findProjectConfig root <&> \case
  ProjectConfig p _ _  -> Just p
  DefaultProjectConfig -> Nothing


-- | Get the content of the @.agda-lib@ file in the given project root.
getAgdaLibFile :: FilePath -> LibM [AgdaLibFile]
getAgdaLibFile path = findProjectConfig path >>= \case
  DefaultProjectConfig          -> return []
  ProjectConfig root file above -> mkLibM [] $
    map (set libAbove above) <$>
    parseLibFiles Nothing [(0, root </> file)]

-- | Get dependencies and include paths for given project root:
--
--   Look for @.agda-lib@ files according to 'findAgdaLibFiles'.
--   If none are found, use default dependencies (according to @defaults@ file)
--   and current directory (project root).
--
getDefaultLibraries
  :: FilePath  -- ^ Project root.
  -> Bool      -- ^ Use @defaults@ if no @.agda-lib@ file exists for this project?
  -> LibM ([LibName], [FilePath])  -- ^ The returned @LibName@s are all non-empty strings.
getDefaultLibraries root optDefaultLibs = do
  libs <- getAgdaLibFile root
  if null libs
    then (,[]) <$> if optDefaultLibs then mkLibM [] $ (libNameForCurrentDir :) <$> readDefaultsFile else return []
    else return $ libsAndPaths libs
  where
    libsAndPaths ls = ( concatMap _libDepends ls
                      , nubOn id (concatMap _libIncludes ls)
                      )

-- | Return list of libraries to be used by default.
--
--   None if the @defaults@ file does not exist.
--
readDefaultsFile :: LibErrorIO [LibName]
readDefaultsFile = do
    agdaDir <- liftIO getAgdaAppDir
    let file = agdaDir </> defaultsFile
    ifNotM (liftIO $ doesFileExist file) (return []) $ {-else-} do
      ls <- liftIO $ map snd . stripCommentLines <$> UTF8.readFile file
      return $ map parseLibName $ concatMap splitCommas ls
  `catchIO` \ e -> do
    raiseErrors' [ ReadError e "Failed to read defaults file." ]
    return []

------------------------------------------------------------------------
-- * Reading the installed libraries
------------------------------------------------------------------------

-- | Returns the path of the @libraries@ file which lists the libraries Agda knows about.
--
--   Note: file may not exist.
--
--   If the user specified an alternative @libraries@ file which does not exist,
--   an exception is thrown containing the name of this file.
getLibrariesFile
  :: (MonadIO m, MonadError FilePath m)
  => Maybe FilePath -- ^ Override the default @libraries@ file?
  -> m LibrariesFile
getLibrariesFile (Just overrideLibFile) = do
  -- A user-specified override file must exist.
  ifM (liftIO $ doesFileExist overrideLibFile)
    {-then-} (return $ LibrariesFile overrideLibFile True)
    {-else-} (throwError overrideLibFile)
getLibrariesFile Nothing = do
  agdaDir <- liftIO $ getAgdaAppDir
  let defaults = List1.map (agdaDir </>) defaultLibraryFiles -- NB: very short list
  files <- liftIO $ filterM doesFileExist (List1.toList defaults)
  case files of
    file : _ -> return $ LibrariesFile file True
    []       -> return $ LibrariesFile (List1.last defaults) False -- doesn't exist, but that's ok

-- | Parse the descriptions of the libraries Agda knows about.
--
--   Returns none if there is no @libraries@ file.
--
getInstalledLibraries
  :: Maybe FilePath     -- ^ Override the default @libraries@ file?
  -> LibM [AgdaLibFile] -- ^ Content of library files.  (Might have empty @LibName@s.)
getInstalledLibraries overrideLibFile = mkLibM [] $ do
    filem <- liftIO $ runExceptT $ getLibrariesFile overrideLibFile
    case filem of
      Left theOverrideLibFile -> do
        raiseErrors' [ LibrariesFileNotFound theOverrideLibFile ]
        return []
      Right file -> do
        if not (lfExists file) then return [] else do
          ls    <- liftIO $ stripCommentLines <$> UTF8.readFile (lfPath file)
          files <- liftIO $ sequence [ (i, ) <$> expandEnvironmentVariables s | (i, s) <- ls ]
          parseLibFiles (Just file) $ nubOn snd files
  `catchIO` \ e -> do
    raiseErrors' [ ReadError e "Failed to read installed libraries." ]
    return []

-- | Parse the given library files.
--
parseLibFiles
  :: Maybe LibrariesFile       -- ^ Name of @libraries@ file for error reporting.
  -> [(LineNumber, FilePath)]  -- ^ Library files paired with their line number in @libraries@.
  -> LibErrorIO [AgdaLibFile]  -- ^ Content of library files.  (Might have empty @LibName@s.)
parseLibFiles mlibFile files = do

  anns <- forM files $ \(ln, file) -> do
    getCachedAgdaLibFile file >>= \case
      Just lib -> return (Right lib, [])
      Nothing  -> do
        (e, ws) <- liftIO $ runP <$> parseLibFile file
        let pos = LibPositionInfo (lfPath <$> mlibFile) ln file
            ws' = map (LibWarning (Just pos)) ws
        case e of
          Left err -> do
            return (Left (Just pos, err), ws')
          Right lib -> do
            storeCachedAgdaLibFile file lib
            return (Right lib, ws')

  let (xs, warns) = unzip anns
      (errs, als) = partitionEithers xs

  List1.unlessNull (concat warns) warnings
  List1.unlessNull errs $ \ errs1 ->
    raiseErrors $ fmap (\ (mc, err) -> LibError mc $ LibParseError err) errs1

  return $ nubOn _libFile als

-- | Remove trailing white space and line comments.
--
stripCommentLines :: String -> [(LineNumber, String)]
stripCommentLines = concatMap strip . zip [1..] . lines
  where
    strip (i, s) = [ (i, s') | not $ null s' ]
      where s' = trimLineComment s

-- | Returns the path of the @executables@ file which lists the trusted executables Agda knows about.
--
--   Note: file may not exist.
--
getExecutablesFile
  :: IO ExecutablesFile
getExecutablesFile = do
  agdaDir <- getAgdaAppDir
  let defaults = List1.map (agdaDir </>) defaultExecutableFiles  -- NB: very short list
  files <- filterM doesFileExist (List1.toList defaults)
  case files of
    file : _ -> return $ ExecutablesFile file True
    []       -> return $ ExecutablesFile (List1.last defaults) False -- doesn't exist, but that's ok

-- | Return the trusted executables Agda knows about.
--
--   Returns none if there is no @executables@ file.
--
getTrustedExecutables
  :: LibM (Map ExeName FilePath)  -- ^ Content of @executables@ files.
getTrustedExecutables = mkLibM [] $ do
    file <- liftIO getExecutablesFile
    if not (efExists file) then return Map.empty else do
      es    <- liftIO $ stripCommentLines <$> UTF8.readFile (efPath file)
      lines <- liftIO $ mapM (mapSndM expandEnvironmentVariables) es
      parseExecutablesFile file lines
  `catchIO` \ e -> do
    raiseErrors' [ ReadError e "Failed to read trusted executables." ]
    return Map.empty

-- | Parse the @executables@ file.
--
parseExecutablesFile
  :: ExecutablesFile
  -> [(LineNumber, FilePath)]
  -> LibErrorIO (Map ExeName FilePath)
parseExecutablesFile ef files = do
  executables <- forM files $ \(ln, fp) -> do
    -- Compute canonical executable name and absolute filepath.
    let strExeName  = takeFileName fp
    let strExeName' = fromMaybe strExeName $ stripExtension exeExtension strExeName
    let txtExeName  = T.pack strExeName'
    exePath <- liftIO $ makeAbsolute fp
    return (txtExeName, (ln, exePath))

  -- Create a map from executable names to their location(s).
  let exeMap1 :: Map ExeName (List1 (LineNumber, FilePath))
      exeMap1 = Map.fromListWith (<>) $ map (second singleton) $ reverse executables

  -- Separate non-ambiguous from ambiguous mappings.
  let (exeMap, duplicates) = Map.mapEither List2.fromList1Either exeMap1

  -- Report ambiguous mappings with line numbers.
  List1.unlessNull (Map.toList duplicates) $ \ duplicates1 ->
    raiseErrors' $ fmap (uncurry $ DuplicateExecutable $ efPath ef) duplicates1

  -- Return non-ambiguous mappings without line numbers.
  return $ fmap snd exeMap

------------------------------------------------------------------------
-- * Resolving library names to include pathes
------------------------------------------------------------------------

-- | Get all include pathes for a list of libraries to use.
libraryIncludePaths
  :: Maybe FilePath  -- ^ @libraries@ file (error reporting only).
  -> [AgdaLibFile]   -- ^ Libraries Agda knows about.
  -> [LibName]       -- ^ (Non-empty) library names to be resolved to (lists of) pathes.
  -> LibM [FilePath] -- ^ Resolved pathes (no duplicates).  Contains "." if @[LibName]@ does.
libraryIncludePaths overrideLibFile libs xs0 = mkLibM libs $ do
    efile <- liftIO $ runExceptT $ getLibrariesFile overrideLibFile
    case efile of
      Left theOverrideLibFile -> do
        raiseErrors' [ LibrariesFileNotFound theOverrideLibFile ]
        return []
      Right file -> embedWriter $ (dot ++) . incs <$> find file [] xs
  where
    (dots, xs) = List.partition (== libNameForCurrentDir) xs0
    incs       = nubOn id . concatMap _libIncludes
    dot        = [ "." | not $ null dots ]

    -- Due to library dependencies, the work list may grow temporarily.
    find
      :: LibrariesFile  -- Only for error reporting.
      -> [LibName]      -- Already resolved libraries.
      -> [LibName]      -- Work list: libraries left to be resolved.
      -> Writer LibErrWarns [AgdaLibFile]
    find _ _ [] = pure []
    find file visited (x : xs)
      | x `elem` visited = find file visited xs
      | otherwise = do
          -- May or may not find the library
          ml <- case findLib x libs of
            [l] -> pure (Just l)
            []  -> Nothing <$ raiseErrors' [LibNotFound file x]
            l1 : l2 : ls  -> Nothing <$ raiseErrors' [AmbiguousLib x $ List2 l1 l2 ls]
          -- If it is found, add its dependencies to work list
          let xs' = foldMap _libDepends ml ++ xs
          mcons ml <$> find file (x : visited) xs'

-- | @findLib x libs@ retrieves the matches for @x@ from list @libs@.
--
--   1. Case @x@ is unversioned:
--      If @x@ is contained in @libs@, then that match is returned.
--      Otherwise, the matches with the highest version number are returned.
--
--   2. Case @x@ is versioned: the matches with the highest version number are returned.
--
--   Examples, see 'findLib''.
--
findLib :: LibName -> [AgdaLibFile] -> [AgdaLibFile]
findLib = findLib' _libName

-- | Generalized version of 'findLib' for testing.
--
--   > findLib' id "a"   [ "a-1", "a-02", "a-2", "b" ] == [ "a-02", "a-2" ]
--
--   > findLib' id "a"   [ "a", "a-1", "a-01", "a-2", "b" ] == [ "a" ]
--   > findLib' id "a-1" [ "a", "a-1", "a-01", "a-2", "b" ] == [ "a-1", "a-01" ]
--   > findLib' id "a-2" [ "a", "a-1", "a-01", "a-2", "b" ] == [ "a-2" ]
--   > findLib' id "c"   [ "a", "a-1", "a-01", "a-2", "b" ] == []
--
findLib' :: (a -> LibName) -> LibName -> [a] -> [a]
findLib' libName x libs =
  case ls of
    -- Take the first and all exact matches (modulo leading zeros in version numbers).
    l : ls' -> l : takeWhile (((==) `on` libName) l) ls'
    []      -> []
  where
    -- @LibName@s that match @x@, sorted descendingly.
    -- The unversioned LibName, if any, will come first.
    ls = List.sortBy (flip compare `on` libName) [ l | l <- libs, x `hasMatch` libName l ]
    -- foo > foo-2.2 > foo-2.0.1 > foo-2 > foo-1.0

-- | @x `hasMatch` y@ if @x@ and @y@ have the same base and
--   either @x@ has no version qualifier or the versions also match.
hasMatch :: LibName -> LibName -> Bool
hasMatch (LibName rx vx) (LibName ry vy) = rx == ry && (vx == vy || null vx)
