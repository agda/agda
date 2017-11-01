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
  ( getDefaultLibraries
  , getInstalledLibraries
  , libraryIncludePaths
  , LibName
  , LibM
  -- * Exported for testing
  , VersionView(..), versionView, unVersionView
  , findLib'
  ) where

import Control.Arrow (first, second)
import Control.Exception
import Control.Monad.Writer
import Data.Char
import Data.Either
import Data.Function
import qualified Data.List as List
import Data.Maybe
import System.Directory ( getAppUserDataDirectory )
import System.Directory
import System.FilePath
import System.Environment

import Agda.Interaction.Library.Base
import Agda.Interaction.Library.Parse

import Agda.Utils.Environment
import Agda.Utils.Except ( ExceptT, runExceptT, MonadError(throwError) )
import Agda.Utils.IO ( catchIO )
import Agda.Utils.List
import Agda.Utils.Maybe
import Agda.Utils.Monad
import Agda.Utils.Pretty
import Agda.Utils.String ( trim, ltrim )

import Agda.Version

------------------------------------------------------------------------
-- Types and Monads
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

-- | Collected errors while processing library files.
--
data LibError
  = LibNotFound FilePath LibName
      -- ^ Raised when a library name could no successfully be resolved
      --   to an @.agda-lib@ file.
  | AmbiguousLib LibName [AgdaLibFile]
      -- ^ Raised when a library name is defined in several @.agda-lib files@.
  | OtherError String
      -- ^ Generic error.
  deriving (Show)

-- | Collects 'LibError's.
--
type LibErrorIO = WriterT [LibError] IO

-- | Throws 'Doc' exceptions.
type LibM = ExceptT Doc IO

-- | Raise collected 'LibErrors' as exception.
--
mkLibM :: [AgdaLibFile] -> LibErrorIO a -> LibM a
mkLibM libs m = do
  (x, err) <- lift $ runWriterT m
  case err of
    [] -> return x
    _  -> throwError =<< do lift $ vcat <$> mapM (formatLibError libs) err

------------------------------------------------------------------------
-- Resources
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

-- | The @~/.agda/libraries@ file lists the libraries Agda should know about.
--   The content of @libraries@ is is a list of pathes to @.agda-lib@ files.
--
--   Agda honors also version specific @libraries@ files, e.g. @libraries-2.6.0@.
--
--   @defaultLibraryFiles@ gives a list of all @libraries@ files Agda should process
--   by default.
--
defaultLibraryFiles :: [FilePath]
defaultLibraryFiles = ["libraries-" ++ version, "libraries"]

-- | The @defaultsFile@ contains a list of library names relevant for each Agda project.
--
defaultsFile :: FilePath
defaultsFile = "defaults"

------------------------------------------------------------------------
-- * Get the libraries for the current project
------------------------------------------------------------------------

-- | Get pathes of @.agda-lib@ files in given project root.
--
--   If there are none, look in the parent directories until one is found.
--
findAgdaLibFiles
  :: FilePath       -- ^ Project root.
  -> IO [FilePath]  -- ^ Pathes of @.agda-lib@ files for this project (if any).
findAgdaLibFiles root = do
  libs <- map (root </>) . filter ((== ".agda-lib") . takeExtension) <$> getDirectoryContents root
  case libs of
    []    -> do
      up <- canonicalizePath $ root </> ".."
      if up == root then return [] else findAgdaLibFiles up
    files -> return files

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
  libs <- lift $ findAgdaLibFiles root
  if null libs
    then (,[]) <$> if optDefaultLibs then (libNameForCurrentDir :) <$> readDefaultsFile else return []
    else libsAndPaths <$> parseLibFiles Nothing (map (0,) libs)
  where
    libsAndPaths ls = (concatMap libDepends ls, concatMap libIncludes ls)

-- | Return list of libraries to be used by default.
--
--   None if the @defaults@ file does not exist.
--
readDefaultsFile :: LibErrorIO [LibName]
readDefaultsFile = do
    agdaDir <- lift $ getAgdaAppDir
    let file = agdaDir </> defaultsFile
    ifNotM (lift $ doesFileExist file) (return []) $ {-else-} do
      ls <- lift $ map snd . stripCommentLines <$> readFile file
      return $ concatMap splitCommas ls
  `catchIO` \ e -> do
    tell [ OtherError $ unlines ["Failed to read defaults file.", show e] ]
    return []

------------------------------------------------------------------------
-- * Reading the installed libraries
------------------------------------------------------------------------

-- | Returns the path of the @libraries@ file which lists the libraries Agda knows about.
--
--   Note: file may not exist.
--
getLibrariesFile
  :: Maybe FilePath -- ^ Override the default @libraries@ file?
  -> IO FilePath
getLibrariesFile (Just overrideLibFile) = return overrideLibFile
getLibrariesFile Nothing = do
  agdaDir <- getAgdaAppDir
  let defaults = map (agdaDir </>) defaultLibraryFiles  -- NB: non-empty list
  files <- filterM doesFileExist defaults
  case files of
    file : _ -> return file
    []       -> return (last defaults) -- doesn't exist, but that's ok

-- | Parse the descriptions of the libraries Agda knows about.
--
--   Returns none if there is no @libraries@ file.
--
getInstalledLibraries
  :: Maybe FilePath  -- ^ Override the default @libraries@ file?
  -> LibM [AgdaLibFile] -- ^ Content of library files.  (Might have empty @LibName@s.)
getInstalledLibraries overrideLibFile = mkLibM [] $ do
    file <- lift $ getLibrariesFile overrideLibFile
    ifNotM (lift $ doesFileExist file) (return []) $ {-else-} do
      ls    <- lift $ stripCommentLines <$> readFile file
      files <- lift $ sequence [ (i, ) <$> expandEnvironmentVariables s | (i, s) <- ls ]
      parseLibFiles (Just file) files
  `catchIO` \ e -> do
    tell [ OtherError $ unlines ["Failed to read installed libraries.", show e] ]
    return []

-- | Parse the given library files.
--
parseLibFiles
  :: Maybe FilePath            -- ^ Name of @libraries@ file for error reporting.
  -> [(LineNumber, FilePath)]  -- ^ Library files paired with their line number in @libraries@.
  -> LibErrorIO [AgdaLibFile]  -- ^ Content of library files.  (Might have empty @LibName@s.)
parseLibFiles libFile files = do
  rs <- lift $ mapM (parseLibFile . snd) files
  -- Format and raise the errors.
  let loc line | Just f <- libFile = f ++ ":" ++ show line ++ ": "
               | otherwise         = ""
  tell [ OtherError $ pos ++ err
       | ((line, path), Left err) <- zip files rs
       , let pos = if List.isPrefixOf "Failed to read" err
                   then loc line
                   else path ++ ":" ++ (if all isDigit (take 1 err) then "" else " ")
       ]
  return $ rights rs

-- | Remove trailing white space and line comments.
--
stripCommentLines :: String -> [(LineNumber, String)]
stripCommentLines = concatMap strip . zip [1..] . lines
  where
    strip (i, s) = [ (i, s') | not $ null s' ]
      where s' = trimLineComment s

-- | Pretty-print 'LibError'.
formatLibError :: [AgdaLibFile] -> LibError -> IO Doc
formatLibError installed = \case

  LibNotFound file lib -> return $ vcat $
    [ text $ "Library '" ++ lib ++ "' not found."
    , sep [ text "Add the path to its .agda-lib file to"
          , nest 2 $ text $ "'" ++ file ++ "'"
          , text "to install."
          ]
    , text "Installed libraries:"
    ] ++
    map (nest 2)
      (if null installed then [text "(none)"]
      else [ sep [ text $ libName l, nest 2 $ parens $ text $ libFile l ] | l <- installed ])

  AmbiguousLib lib tgts -> return $ vcat $
    [ sep [ text $ "Ambiguous library '" ++ lib ++ "'.", text "Could refer to any one of" ]
    ] ++ [ nest 2 $ text (libName l) <+> parens (text $ libFile l) | l <- tgts ]

  OtherError err -> return $ text err

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
    file <- getLibrariesFile overrideLibFile
    return $ runWriter $ (dot ++) . incs <$> find file [] xs
  where
    (dots, xs) = List.partition (== libNameForCurrentDir) $ map trim xs0
    incs = List.nub . concatMap libIncludes
    dot = [ "." | not $ null dots ]

    -- | Due to library dependencies, the work list may grow temporarily.
    find
      :: FilePath   -- ^ Only for error reporting.
      -> [LibName]  -- ^ Already resolved libraries.
      -> [LibName]  -- ^ Work list: libraries left to be resolved.
      -> Writer [LibError] [AgdaLibFile]
    find _ _ [] = pure []
    find file visited (x : xs)
      | elem x visited = find file visited xs
      | otherwise =
          case findLib x libs of
            [l] -> (l :) <$> find file (x : visited) (libDepends l ++ xs)
            []  -> tell [LibNotFound file x] >> find file (x : visited) xs
            ls  -> tell [AmbiguousLib x ls]  >> find file (x : visited) xs

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
findLib = findLib' libName

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
    ls = List.sortBy (flip compare `on` versionMeasure) [ l | l <- libs, x `hasMatch` libName l ]

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
