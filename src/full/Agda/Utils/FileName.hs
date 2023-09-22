{-# LANGUAGE CPP                        #-}

{-| Operations on file names. -}
module Agda.Utils.FileName
  ( AbsolutePath(AbsolutePath)
  , filePath
  , mkAbsolute
  , absolute
  , canonicalizeAbsolutePath
  , sameFile
  , doesFileExistCaseSensitive
  , isNewerThan
  , relativizeAbsolutePath
  ) where

import System.Directory
import System.FilePath

import Control.Applicative ( liftA2 )
import Control.DeepSeq
#ifdef mingw32_HOST_OS
import Control.Exception   ( bracket )
import System.Win32        ( findFirstFile, findClose, getFindDataFileName )
#endif

import Data.Function (on)
import Data.Hashable       ( Hashable )
import Data.Text           ( Text )
import qualified Data.Text as Text

import Agda.Utils.Monad
import Agda.Syntax.Common.Pretty

import Agda.Utils.Impossible

-- | Paths which are known to be absolute.
--
-- Note that the 'Eq' and 'Ord' instances do not check if different
-- paths point to the same files or directories.

newtype AbsolutePath = AbsolutePath { textPath :: Text }
  deriving (Show, Eq, Ord, Hashable, NFData)

-- | Extract the 'AbsolutePath' to be used as 'FilePath'.
filePath :: AbsolutePath -> FilePath
filePath = Text.unpack . textPath

instance Pretty AbsolutePath where
  pretty = text . filePath

-- | Constructs 'AbsolutePath's.
--
-- Precondition: The path must be absolute and valid.

mkAbsolute :: FilePath -> AbsolutePath
mkAbsolute f
  | isAbsolute f =
      AbsolutePath $ Text.pack $ dropTrailingPathSeparator $ normalise f
        -- normalize does not resolve symlinks
  | otherwise    = __IMPOSSIBLE__

-- UNUSED Liang-Ting Chen 2019-07-16
---- | maps @/bla/bla/bla/foo.bar.xxx@ to @foo.bar@.
--rootName :: AbsolutePath -> String
--rootName = dropExtension . snd . splitFileName . filePath

-- | Makes the path absolute.
--
-- This function may raise an @\_\_IMPOSSIBLE\_\_@ error if
-- 'canonicalizePath' does not return an absolute path.

absolute :: FilePath -> IO AbsolutePath
absolute f = mkAbsolute <$> do
  -- canonicalizePath sometimes truncates paths pointing to
  -- non-existing files/directories.
  ex <- doesFileExist f `or2M` doesDirectoryExist f
  if ex then do
    -- Andreas, 2020-08-11, issue #4828
    -- Do not use @canonicalizePath@ on the full path as it resolves symlinks,
    -- which leads to wrong placement of the .agdai file.
    dir <- canonicalizePath (takeDirectory f)
    return (dir </> takeFileName f)
   else do
    cwd <- getCurrentDirectory
    return (cwd </> f)

-- | Resolve symlinks etc.  Preserves 'sameFile'.

canonicalizeAbsolutePath :: AbsolutePath -> IO AbsolutePath
canonicalizeAbsolutePath (AbsolutePath f) =
  AbsolutePath . Text.pack <$> canonicalizePath (Text.unpack f)

-- | Tries to establish if the two file paths point to the same file
-- (or directory). False negatives may be returned.

sameFile :: AbsolutePath -> AbsolutePath -> IO Bool
sameFile = liftA2 equalFilePath `on` (canonicalizePath . filePath)

-- | Case-sensitive 'doesFileExist' for Windows.
--
-- This is case-sensitive only on the file name part, not on the directory part.
-- (Ideally, path components coming from module name components should be
--  checked case-sensitively and the other path components should be checked
--  case insensitively.)

doesFileExistCaseSensitive :: FilePath -> IO Bool
#ifdef mingw32_HOST_OS
doesFileExistCaseSensitive f = do
  doesFileExist f `and2M` do
    bracket (findFirstFile f) (findClose . fst) $
      fmap (takeFileName f ==) . getFindDataFileName . snd
#else
doesFileExistCaseSensitive = doesFileExist
#endif

-- | True if the first file is newer than the second file. If a file doesn't
-- exist it is considered to be infinitely old.
isNewerThan :: FilePath -> FilePath -> IO Bool
isNewerThan new old = do
    newExist <- doesFileExist new
    oldExist <- doesFileExist old
    if not (newExist && oldExist)
        then return newExist
        else do
            newT <- getModificationTime new
            oldT <- getModificationTime old
            return $ newT >= oldT

-- | A partial version of 'System.FilePath.makeRelative' with flipped arguments,
--   returning 'Nothing' if the given path cannot be relativized to the given @root@.
relativizeAbsolutePath ::
     AbsolutePath
       -- ^ The absolute path we see to relativize.
  -> AbsolutePath
       -- ^ The root for relativization.
  -> Maybe FilePath
       -- ^ The relative path, if any.
relativizeAbsolutePath apath aroot
  | rest /= path = Just rest
  | otherwise    = Nothing
  where
  path = filePath apath
  root = filePath aroot
  rest = makeRelative root path
    -- Andreas, 2022-10-10
    -- See https://gitlab.haskell.org/haskell/filepath/-/issues/130.
    -- 'System.FilePath.makeRelative' is strangely enough a total function,
    -- and it returns the original @path@ if it could not be relativized to
    -- the @root@, or if the @root@ was ".".
    -- In our case, the @root@ is absolute, so we should expect @rest@ to
    -- always be different from @path@ if @path@ is relative to @root@.
    -- In the extreme case, @root = "/"@ and @path == "/" ++ rest@.
