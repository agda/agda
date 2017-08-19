
module Agda.Interaction.Library
  ( getDefaultLibraries
  , getInstalledLibraries
  , libraryIncludePaths
  , LibName
  , LibM
  -- * Testing
  , VersionView(..), versionView, unVersionView
  , findLib'
  ) where

import Control.Arrow (first, second)
import Control.Applicative
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

type LibM = ExceptT Doc IO

-- | Library names are structured into the base name and a suffix of version
--   numbers, e.g. @mylib-1.2.3@.  The version suffix is optional.
data VersionView = VersionView
  { vvBase    :: LibName
      -- ^ Actual library name.
  , vvNumbers :: [Integer]
      -- ^ Major version, minor version, subminor version, etc., all non-negative.
      --   Note: a priori, there is no reason why the version numbers should be @Int@s.
  } deriving (Eq, Show)

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

data LibError
  = LibNotFound FilePath LibName
      -- ^ Raised when a library name could no successfully be resolved
      --   to an @.agda-lib@ file.
  | AmbiguousLib LibName [AgdaLibFile]
      -- ^ Raised when a library name is defined in several @.agda-lib files@.
  | OtherError String
      -- ^ Generic error.
  deriving (Show)

mkLibM :: [AgdaLibFile] -> IO (a, [LibError]) -> LibM a
mkLibM libs m = do
  (x, err) <- lift m
  case err of
    [] -> return x
    _  -> throwError =<< lift (vcat <$> mapM (formatLibError libs) err)

findAgdaLibFiles :: FilePath -> IO [FilePath]
findAgdaLibFiles root = do
  libs <- map (root </>) . filter ((== ".agda-lib") . takeExtension) <$> getDirectoryContents root
  case libs of
    []    -> do
      up <- canonicalizePath $ root </> ".."
      if up == root then return [] else findAgdaLibFiles up
    files -> return files

getDefaultLibraries :: FilePath -> Bool -> LibM ([LibName], [FilePath])
getDefaultLibraries root optDefaultLibs = mkLibM [] $ do
  libs <- findAgdaLibFiles root
  if null libs
    then
    if optDefaultLibs then first (, []) <$> readDefaultsFile else return (([], []), [])
    else first libsAndPaths <$> parseLibFiles Nothing (zip (repeat 0) libs)
  where
    libsAndPaths ls = (concatMap libDepends ls, concatMap libIncludes ls)

readDefaultsFile :: IO ([LibName], [LibError])
readDefaultsFile = do
    agdaDir <- getAgdaAppDir
    let file = agdaDir </> defaultsFile
    ifM (doesFileExist file) (do
      ls <- map snd . stripCommentLines <$> readFile file
      return ("." : concatMap splitCommas ls, [])
      ) {- else -} (return (["."], []))
  `catchIO` \e -> return (["."], [OtherError $ "Failed to read defaults file.\n" ++ show e])

getLibrariesFile :: Maybe FilePath -> IO FilePath
getLibrariesFile (Just overrideLibFile) = return overrideLibFile
getLibrariesFile Nothing = do
  agdaDir <- getAgdaAppDir
  let defaults = map (agdaDir </>) defaultLibraryFiles
  files <- filterM doesFileExist defaults
  case files of
    file : _ -> return file
    []       -> return (last defaults) -- doesn't exist, but that's ok

getInstalledLibraries :: Maybe FilePath -> LibM [AgdaLibFile]
getInstalledLibraries overrideLibFile = mkLibM [] $ do
    file <- getLibrariesFile overrideLibFile
    ifM (doesFileExist file) (do
      ls    <- stripCommentLines <$> readFile file
      files <- sequence [ (i, ) <$> expandEnvironmentVariables s | (i, s) <- ls ]
      parseLibFiles (Just file) files
      ) {- else -} (return ([], []))
  `catchIO` \e -> return ([], [OtherError $ "Failed to read installed libraries.\n" ++ show e])

parseLibFiles :: Maybe FilePath -> [(Int, FilePath)] -> IO ([AgdaLibFile], [LibError])
parseLibFiles libFile files = do
  rs <- mapM (parseLibFile . snd) files
  let loc line | Just f <- libFile = f ++ ":" ++ show line ++ ": "
               | otherwise         = ""
      errs = [ if List.isPrefixOf "Failed to read" err
                then OtherError $ loc line ++ err
                else OtherError $ path ++ ":" ++ (if all isDigit (take 1 err) then "" else " ") ++ err
             | ((line, path), Left err) <- zip files rs ]
  return (rights rs, errs)

stripCommentLines :: String -> [(Int, String)]
stripCommentLines = concatMap strip . zip [1..] . lines
  where
    strip (i, s) = [ (i, s') | not $ null s' ]
      where s' = trimLineComment s

formatLibError :: [AgdaLibFile] -> LibError -> IO Doc
formatLibError installed (LibNotFound file lib) = do
  return $ vcat $
    [ text $ "Library '" ++ lib ++ "' not found."
    , sep [ text "Add the path to its .agda-lib file to"
          , nest 2 $ text $ "'" ++ file ++ "'"
          , text "to install." ]
    , text "Installed libraries:"
    ] ++
    map (nest 2)
      (if null installed then [text "(none)"]
      else [ sep [ text $ libName l, nest 2 $ parens $ text $ libFile l ] | l <- installed ])
formatLibError _ (AmbiguousLib lib tgts) = return $
  vcat $ sep [ text $ "Ambiguous library '" ++ lib ++ "'."
             , text "Could refer to any one of" ]
       : [ nest 2 $ text (libName l) <+> parens (text $ libFile l) | l <- tgts ]
formatLibError _ (OtherError err) = return $ text err

libraryIncludePaths :: Maybe FilePath -> [AgdaLibFile] -> [LibName] -> LibM [FilePath]
libraryIncludePaths overrideLibFile libs xs0 = mkLibM libs $ do
    file <- getLibrariesFile overrideLibFile
    return $ runWriter ((dot ++) . incs <$> find file [] xs)
  where
    xsTr = map trim xs0
    xs   = List.delete "." xsTr
    incs = List.nub . concatMap libIncludes
    dot  = [ "." | elem "." xsTr ]

    find :: FilePath -> [LibName] -> [LibName] -> Writer [LibError] [AgdaLibFile]
    find _ _ [] = pure []
    find file visited (x : xs)
      | elem x visited = find file visited xs
      | otherwise =
          case findLib x libs of
            [l] -> (l :) <$> find file (x : visited) (libDepends l ++ xs)
            []  -> tell [LibNotFound file x] >> find file (x : visited) xs
            ls  -> tell [AmbiguousLib x ls] >> find file (x : visited) xs

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
--   @
--     findLib' id "a"   [ "a-1", "a-02", "a-2", "b" ] == [ "a-02", "a-2" ]
--
--     findLib' id "a"   [ "a", "a-1", "a-01", "a-2", "b" ] == [ "a" ]
--     findLib' id "a-1" [ "a", "a-1", "a-01", "a-2", "b" ] == [ "a-1", "a-01" ]
--     findLib' id "a-2" [ "a", "a-1", "a-01", "a-2", "b" ] == [ "a-2" ]
--     findLib' id "c"   [ "a", "a-1", "a-01", "a-2", "b" ] == []
--   @
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
--   @
--     versionView "foo-1.2.3"    == VersionView "foo" [1, 2, 3]
--     versionView "foo-01.002.3" == VersionView "foo" [1, 2, 3]
--   @
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
