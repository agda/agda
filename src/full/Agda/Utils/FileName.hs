{-# LANGUAGE CPP                        #-}

{-| Operations on file names. -}
module Agda.Utils.FileName
  ( Path(..)
  , filePath
  , mkPath
  , sameFile
  , removeSomeDuplicates
  , removeSomeDuplicatesFP
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

import Data.Function
import Data.Hashable       ( Hashable )
import qualified Data.List as List
import Data.Text           ( Text )
import qualified Data.Text as Text

import Agda.Utils.List
import Agda.Utils.Monad
import Agda.Utils.Pretty

import Agda.Utils.Impossible

-- | Paths.
--
-- Note that the 'Eq' and 'Ord' instances do not check if different
-- paths point to the same files or directories.

newtype Path = Path { textPath :: Text }
  deriving (Show, Eq, Ord, Hashable, NFData)

-- | Converts 'Path's to 'FilePath's.
filePath :: Path -> FilePath
filePath = Text.unpack . textPath

instance Pretty Path where
  pretty = text . filePath

-- | Constructs 'Path's.
--
-- Some normalisation is performed.
--
-- Precondition: The path must be valid.

mkPath :: FilePath -> Path
mkPath =
  Path . Text.pack . dropTrailingPathSeparator . normalise

-- UNUSED Liang-Ting Chen 2019-07-16
---- | maps @/bla/bla/bla/foo.bar.xxx@ to @foo.bar@.
--rootName :: Path -> String
--rootName = dropExtension . snd . splitFileName . filePath

-- | Tries to establish if the two file paths point to the same file
-- (or directory). False negatives may be returned.

sameFile :: Path -> Path -> IO Bool
sameFile f1 f2 =
  or2M (return (f1 == f2))
    ((liftA2 equalFilePath `on` canonicalizePath . filePath) f1 f2)

-- | Tries to remove duplicate paths, where a path is a duplicate of
-- another if they both refer to the same file or directory. Some
-- duplicates may exist in the output.
--
-- If there is a choice between keeping a relative or an absolute
-- path, then the relative one is kept, and if there is a choice
-- between two relative or two absolute paths, then the shorter one is
-- kept (and if the paths have the same length, then the one that is
-- first in the list is kept).
--
-- Paths that are kept are not reordered.

removeSomeDuplicates :: [Path] -> IO [Path]
removeSomeDuplicates =
  removeSomeDuplicates' . map (\p -> (p, filePath p))

-- | A variant of 'removeSomeDuplicates'.

removeSomeDuplicatesFP :: [FilePath] -> IO [Path]
removeSomeDuplicatesFP =
  removeSomeDuplicates' . map (\p -> (mkPath p, p))

-- | A generalisation of 'removeSomeDuplicates'.
--
-- The two paths in a pair should refer to the same file or directory.

removeSomeDuplicates' :: [(Path, FilePath)] -> IO [Path]
removeSomeDuplicates' ps =
  case nubOn fst ps of
    ps@(_ : _ : _) ->
      map (fst . fst) .
      nubFavouriteOn
        (\((_, f), _) -> (not (isRelative f), length f))
        snd <$>
      mapM (\p@(_, f) -> (p,) <$> canonicalizePath f) ps
    ps -> return (map fst ps)

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
     Path
       -- ^ The absolute path we see to relativize.
  -> Path
       -- ^ The root for relativization.
       --
       -- Precondition: This path should be absolute.
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
