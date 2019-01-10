{-# LANGUAGE CPP                        #-}
{-# LANGUAGE DeriveDataTypeable         #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}

{-| Operations on file names. -}
module Agda.Utils.FileName
  ( AbsolutePath(AbsolutePath)
  , filePath
  , mkAbsolute
  , absolute
  , (===)
  , doesFileExistCaseSensitive
  , rootPath
  , prefixPath
  ) where

import System.Directory
import System.FilePath

#ifdef mingw32_HOST_OS
import Control.Exception (bracket)
import System.Win32 (findFirstFile, findClose, getFindDataFileName)
#endif

import Data.Text (Text)
import qualified Data.Text as Text
import Data.Function
import Data.Hashable (Hashable)
import Data.Data (Data)
import Data.List (isPrefixOf)

import Agda.Utils.Monad
import Agda.Utils.Pretty

#include "undefined.h"
import Agda.Utils.Impossible

-- | Paths which are known to be absolute.
--
-- Note that the 'Eq' and 'Ord' instances do not check if different
-- paths point to the same files or directories.

newtype AbsolutePath = AbsolutePath { byteStringPath :: Text }
  deriving (Eq, Ord, Data, Hashable)

-- | Extract the 'AbsolutePath' to be used as 'FilePath'.
filePath :: AbsolutePath -> FilePath
filePath = Text.unpack . byteStringPath

-- TODO: 'Show' should output Haskell-parseable representations.
-- The following instance is deprecated, and Pretty should be used
-- instead.  Later, simply derive Show for this type.

instance Show AbsolutePath where
  show = filePath

instance Pretty AbsolutePath where
  pretty = text . filePath

-- | Constructs 'AbsolutePath's.
--
-- Precondition: The path must be absolute and valid.

mkAbsolute :: FilePath -> AbsolutePath
mkAbsolute f
  | isAbsolute f =
      AbsolutePath $ Text.pack $ dropTrailingPathSeparator $ normalise f
  | otherwise    = __IMPOSSIBLE__

rootPath :: FilePath
#ifdef mingw32_HOST_OS
rootPath = joinDrive "C:" [pathSeparator]
#else
rootPath = [pathSeparator]
#endif

-- | maps @/bla/bla/bla/foo.bar.xxx@ to @foo.bar@.
rootName :: AbsolutePath -> String
rootName = dropExtension . snd . splitFileName . filePath

-- | Makes the path absolute.
--
-- This function may raise an @\_\_IMPOSSIBLE\_\_@ error if
-- 'canonicalizePath' does not return an absolute path.

absolute :: FilePath -> IO AbsolutePath
absolute f = mkAbsolute <$> do
  -- canonicalizePath sometimes truncates paths pointing to
  -- non-existing files/directories.
  ex <- doesFileExist f .||. doesDirectoryExist f
  if ex then
    canonicalizePath f
   else do
    cwd <- getCurrentDirectory
    return (cwd </> f)
  where
  m1 .||. m2 = do
    b1 <- m1
    if b1 then return True else m2

-- | Tries to establish if the two file paths point to the same file
-- (or directory).

infix 4 ===

(===) :: AbsolutePath -> AbsolutePath -> Bool
(===) = equalFilePath `on` filePath

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
doesFileExistCaseSensitive f = doesFileExist f
#endif

prefixPath :: FilePath -> FilePath -> Bool
prefixPath f f' = (splitDirectories f) `isPrefixOf` (splitDirectories f')
