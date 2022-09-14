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
  , getAgdaLibFiles'
  , getPrimitiveLibDir
  , LibName
  , AgdaLibFile(..)
  , ExeName
  , LibM
  , mkLibM
  , LibWarning(..)
  , LibPositionInfo(..)
  , libraryWarningName
  , ProjectConfig(..)
  -- * Exported for testing
  , VersionView(..), versionView, unVersionView
  , findLib'
  ) where

import Control.Arrow          ( first , second )
import Control.Monad          ( filterM, forM )
import Control.Monad.Except
import Control.Monad.State
import Control.Monad.Writer
import Control.Monad.IO.Class ( MonadIO(..) )

import Data.Char
import Data.Either
import Data.Function
import Data.Map ( Map )
import qualified Data.Map as Map
import Data.Maybe ( catMaybes, fromMaybe )
import qualified Data.List as List
import qualified Data.Text as T

import System.Directory
import System.FilePath
import System.Environment
import Text.Printf

import Agda.Interaction.Library.Base
import Agda.Interaction.Library.Parse
import Agda.Interaction.Options.Warnings

import Agda.Utils.Environment
import Agda.Utils.FileName
import Agda.Utils.Functor ( (<&>) )
import Agda.Utils.IO ( catchIO )
import qualified Agda.Utils.IO.UTF8 as UTF8
import Agda.Utils.List
import Agda.Utils.List1 ( List1, pattern (:|) )
import qualified Agda.Utils.List1 as List1
import Agda.Utils.Maybe
import Agda.Utils.Monad
import Agda.Utils.Pretty
import Agda.Utils.String ( trim )

import Agda.Version

-- Paths_Agda.hs is in $(BUILD_DIR)/build/autogen/.
import Paths_Agda ( getDataFileName )

------------------------------------------------------------------------
-- * Types and Monads
------------------------------------------------------------------------

-- | Library names are structured into the base name and a suffix of version
--   numbers, e.g. @mylib-1.2.3@.  The version suffix is optional.
data VersionView = VersionView
  { vvBase    :: LibName
      -- ^ Actual library name.
  , vvNumbers :: [Integer]
      -- ^ Major version, minor version, subminor version, etc., all non-negative.
      --   Note: a priori, there is no reason why the version numbers should be @Int@s.
  } deriving (Eq, Show)

-- | Raise collected 'LibErrors' as exception.
--
mkLibM :: [AgdaLibFile] -> LibErrorIO a -> LibM a
mkLibM libs m = do
  (x, ews) <- lift $ lift $ runWriterT m
  let (errs, warns) = partitionEithers ews
  tell warns
  unless (null errs) $ do
    let doc = vcat $ map (formatLibError libs) errs
    throwError doc
  return x

------------------------------------------------------------------------
-- * Resources
------------------------------------------------------------------------

-- | Get the path to @~/.agda@ (system-specific).
--   Can be overwritten by the @AGDA_DIR@ environment variable.
--
--   (This is not to be confused with the directory for the data files
--   that Agda needs (e.g. the primitive modules).)
--
getAgdaAppDir :: IO FilePath
getAgdaAppDir = do
  -- System-specific command to build the path to ~/.agda (Unix) or %APPDATA%\agda (Win)
  let agdaDir = getAppUserDataDirectory "agda"
  -- The default can be overwritten by setting the AGDA_DIR environment variable
  caseMaybeM (lookupEnv "AGDA_DIR") agdaDir $ \ dir ->
      ifM (doesDirectoryExist dir) (canonicalizePath dir) $ do
        d <- agdaDir
        putStrLn $ "Warning: Environment variable AGDA_DIR points to non-existing directory " ++ show dir ++ ", using " ++ show d ++ " instead."
        return d

-- | Returns the absolute default lib dir. This directory is used to
-- store the Primitive.agda file.
getPrimitiveLibDir :: IO FilePath
getPrimitiveLibDir = do
  libdir <- filePath <$> (absolute =<< getDataFileName "lib")
  ifM (doesDirectoryExist libdir)
      (return $ libdir </> "prim")
      (error $ "The lib directory " ++ libdir ++ " does not exist")

-- | The @~/.agda/libraries@ file lists the libraries Agda should know about.
--   The content of @libraries@ is a list of paths to @.agda-lib@ files.
--
--   Agda honors also version specific @libraries@ files, e.g. @libraries-2.6.0@.
--
--   @defaultLibraryFiles@ gives a list of all @libraries@ files Agda should process
--   by default.
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
--   Agda honors also version specific @executables@ files, e.g. @executables-2.6.0@.
--
--   @defaultExecutablesFiles@ gives a list of all @executables@ Agda should process
--   by default.
--
defaultExecutableFiles :: List1 FilePath
defaultExecutableFiles = ("executables-" ++ version) :| "executables" : []

------------------------------------------------------------------------
-- * Get the libraries for the current project
------------------------------------------------------------------------

-- | Find project root by looking for @.agda-lib@ files.
--
--   If there are none, look in the parent directories until one is found.

findProjectConfig
  :: FilePath                          -- ^ Candidate (init: the directory Agda was called in)
  -> LibM ProjectConfig                -- ^ Actual root and @.agda-lib@ files for this project
findProjectConfig root = mkLibM [] $ findProjectConfig' root

findProjectConfig'
  :: FilePath                          -- ^ Candidate (init: the directory Agda was called in)
  -> LibErrorIO ProjectConfig          -- ^ Actual root and @.agda-lib@ files for this project
findProjectConfig' root = do
  getCachedProjectConfig root >>= \case
    Just conf -> return conf
    Nothing   -> do
      libFiles <- liftIO $ filter ((== ".agda-lib") . takeExtension) <$> getDirectoryContents root
      case libFiles of
        []     -> liftIO (upPath root) >>= \case
          Just up -> do
            conf <- findProjectConfig' up
            storeCachedProjectConfig root conf
            return conf
          Nothing -> return DefaultProjectConfig
        files -> do
          let conf = ProjectConfig root files
          storeCachedProjectConfig root conf
          return conf

  where
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
  ProjectConfig p _    -> Just p
  DefaultProjectConfig -> Nothing


-- | Get the contents of @.agda-lib@ files in the given project root.
getAgdaLibFiles' :: FilePath -> LibErrorIO [AgdaLibFile]
getAgdaLibFiles' path = findProjectConfig' path >>= \case
  DefaultProjectConfig    -> return []
  ProjectConfig root libs -> parseLibFiles Nothing $ map ((0,) . (root </>)) libs

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
getDefaultLibraries root optDefaultLibs = mkLibM [] $ do
  libs <- getAgdaLibFiles' root
  if null libs
    then (,[]) <$> if optDefaultLibs then (libNameForCurrentDir :) <$> readDefaultsFile else return []
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
      return $ concatMap splitCommas ls
  `catchIO` \ e -> do
    raiseErrors' [ OtherError $ unlines ["Failed to read defaults file.", show e] ]
    return []

------------------------------------------------------------------------
-- * Reading the installed libraries
------------------------------------------------------------------------

-- | Returns the path of the @libraries@ file which lists the libraries Agda knows about.
--
--   Note: file may not exist.
--
getLibrariesFile
  :: (MonadIO m, MonadError String m)
  => Maybe FilePath -- ^ Override the default @libraries@ file?
  -> m LibrariesFile
getLibrariesFile (Just overrideLibFile) = do
  -- A user-specified override file must exist.
  ifM (liftIO $ doesFileExist overrideLibFile)
    {-then-} (return $ LibrariesFile overrideLibFile True)
    {-else-} (throwError $ "Libraries file not found: " ++ overrideLibFile)
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
      Left err -> raiseErrors' [OtherError err] >> return []
      Right file -> do
        if not (lfExists file) then return [] else do
          ls    <- liftIO $ stripCommentLines <$> UTF8.readFile (lfPath file)
          files <- liftIO $ sequence [ (i, ) <$> expandEnvironmentVariables s | (i, s) <- ls ]
          parseLibFiles (Just file) $ nubOn snd files
  `catchIO` \ e -> do
    raiseErrors' [ OtherError $ unlines ["Failed to read installed libraries.", show e] ]
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

  unless (null warns) $ warnings $ concat warns
  unless (null errs)  $
    raiseErrors $ map (\(mc,s) -> LibError mc $ OtherError s) errs

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
      files <- liftIO $ sequence [ (i, ) <$> expandEnvironmentVariables s | (i, s) <- es ]
      tmp   <- parseExecutablesFile file $ nubOn snd files
      return tmp
  `catchIO` \ e -> do
    raiseErrors' [ OtherError $ unlines ["Failed to read trusted executables.", show e] ]
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
    return (txtExeName, exePath)
  let exeMap = Map.fromList executables
      -- Issue #5525: check for duplicate entries in executables file
      duplicates = [ (exe, paths)
                   | exe <- Map.keys exeMap
                   , let paths = [ path | (exe', path) <- executables
                                        , exe' == exe ]
                   , length paths > 1 ]
  when (not $ null duplicates) $
    raiseErrors' [ OtherError $ unlines
                              $ (printf "Duplicate entries for executable '%s' in %s:" exe (efPath ef))
                              : [ "  - " ++ path | path <- paths ]
                 | (exe, paths) <- duplicates ]
  return $ Map.fromList executables

------------------------------------------------------------------------
-- * Resolving library names to include pathes
------------------------------------------------------------------------

-- | Get all include pathes for a list of libraries to use.
libraryIncludePaths
  :: Maybe FilePath  -- ^ @libraries@ file (error reporting only).
  -> [AgdaLibFile]   -- ^ Libraries Agda knows about.
  -> [LibName]       -- ^ (Non-empty) library names to be resolved to (lists of) pathes.
  -> LibM [FilePath] -- ^ Resolved pathes (no duplicates).  Contains "." if @[LibName]@ does.
libraryIncludePaths overrideLibFile libs xs0 = mkLibM libs $ WriterT $ do
    efile <- liftIO $ runExceptT $ getLibrariesFile overrideLibFile
    case efile of
      Left err -> return ([], [Left $ LibError Nothing $ OtherError err])
      Right file -> return $ runWriter $ (dot ++) . incs <$> find file [] xs
  where
    (dots, xs) = List.partition (== libNameForCurrentDir) $ map trim xs0
    incs       = nubOn id . concatMap _libIncludes
    dot        = [ "." | not $ null dots ]

    -- Due to library dependencies, the work list may grow temporarily.
    find
      :: LibrariesFile  -- Only for error reporting.
      -> [LibName]      -- Already resolved libraries.
      -> [LibName]      -- Work list: libraries left to be resolved.
      -> Writer [Either LibError LibWarning] [AgdaLibFile]
    find _ _ [] = pure []
    find file visited (x : xs)
      | x `elem` visited = find file visited xs
      | otherwise = do
          -- May or may not find the library
          ml <- case findLib x libs of
            [l] -> pure (Just l)
            []  -> Nothing <$ raiseErrors' [LibNotFound file x]
            ls  -> Nothing <$ raiseErrors' [AmbiguousLib x ls]
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
    l : ls' -> l : takeWhile (((==) `on` versionMeasure) l) ls'
    []      -> []
  where
    -- @LibName@s that match @x@, sorted descendingly.
    -- The unversioned LibName, if any, will come first.
    ls = List.sortBy (flip compare `on` versionMeasure)
                     [ l | l <- libs, x `hasMatch` libName l ]

    -- foo > foo-2.2 > foo-2.0.1 > foo-2 > foo-1.0
    versionMeasure l = (rx, null vs, vs)
      where
        VersionView rx vs = versionView (libName l)

-- | @x `hasMatch` y@ if @x@ and @y@ have the same @vvBase@ and
--   either @x@ has no version qualifier or the versions also match.
hasMatch :: LibName -> LibName -> Bool
hasMatch x y = rx == ry && (vx == vy || null vx)
  where
    VersionView rx vx = versionView x
    VersionView ry vy = versionView y

-- | Split a library name into basename and a list of version numbers.
--
--   > versionView "foo-1.2.3"    == VersionView "foo" [1, 2, 3]
--   > versionView "foo-01.002.3" == VersionView "foo" [1, 2, 3]
--
--   Note that because of leading zeros, @versionView@ is not injective.
--   (@unVersionView . versionView@ would produce a normal form.)
versionView :: LibName -> VersionView
versionView s =
  case span (\ c -> isDigit c || c == '.') (reverse s) of
    (v, '-' : x) | valid vs ->
      VersionView (reverse x) $ reverse $ map (read . reverse) vs
      where vs = chopWhen (== '.') v
            valid [] = False
            valid vs = not $ any null vs
    _ -> VersionView s []

-- | Print a @VersionView@, inverse of @versionView@ (modulo leading zeros).
unVersionView :: VersionView -> LibName
unVersionView = \case
  VersionView base [] -> base
  VersionView base vs -> base ++ "-" ++ List.intercalate "." (map show vs)
