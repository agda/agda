{-# LANGUAGE CPP #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE DeriveGeneric #-}

{-| Operations on file names. -}
module Agda.Utils.FileName
  ( AbsolutePath
  , filePath
  , rootName
  , mkAbsolute
  , absolute
  , (===)
  , doesFileExistCaseSensitive
  , tests
  ) where

import GHC.Generics (Generic)

import Control.Applicative
import System.Directory
import System.FilePath

#if mingw32_HOST_OS
import Control.Exception (bracket)
import System.Win32 (findFirstFile, findClose, getFindDataFileName)
#endif

import Data.ByteString.Char8 (ByteString)
import qualified Data.ByteString.Char8 as ByteString
import Data.Function
import Data.Typeable (Typeable)

import Agda.Utils.Pretty
import Agda.Utils.TestHelpers
import Agda.Utils.QuickCheck

#include "undefined.h"
import Agda.Utils.Impossible

-- | Paths which are known to be absolute.
--
-- Note that the 'Eq' and 'Ord' instances do not check if different
-- paths point to the same files or directories.
--
-- Andreas, 2014-03-30:
-- For efficiency of serialization, 'AbsolutePath' is implemented
-- as 'ByteString' which short-cuts equality testing using
-- pointer equality.  This saves 20% of the serialization time
-- of the standard library!

newtype AbsolutePath = AbsolutePath { byteStringPath :: ByteString }
  deriving (Eq, Ord, Typeable, Generic)

-- | Extract the 'AbsolutePath' to be used as 'FilePath'.
filePath :: AbsolutePath -> FilePath
filePath = ByteString.unpack . byteStringPath

-- TODO: 'Show' should output Haskell-parseable representations.
-- The following instance is deprecated, and Pretty should be used
-- instead.  Later, simply derive Show for this type.

instance Show AbsolutePath where
  show = filePath

instance Pretty AbsolutePath where
  pretty = text . filePath

-- | The paths have to be absolute, valid and normalised, without
-- trailing path separators.

absolutePathInvariant :: AbsolutePath -> Bool
absolutePathInvariant x =
  isAbsolute f &&
  isValid f &&
  f == normalise f &&
  f == dropTrailingPathSeparator f
  where f = filePath x

-- | Constructs 'AbsolutePath's.
--
-- Precondition: The path must be absolute and valid.

mkAbsolute :: FilePath -> AbsolutePath
mkAbsolute f
  | isAbsolute f =
      AbsolutePath $ ByteString.pack $ dropTrailingPathSeparator $ normalise f
  | otherwise    = __IMPOSSIBLE__

#if mingw32_HOST_OS
prop_mkAbsolute :: FilePath -> Property
#else
prop_mkAbsolute :: FilePath -> Bool
#endif
prop_mkAbsolute f =
  let path = rootPath ++ f
  in
#if mingw32_HOST_OS
      isValid path ==>
#endif
      absolutePathInvariant $ mkAbsolute $ path

rootPath :: FilePath
#if mingw32_HOST_OS
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

-- | Case-sensitive doesFileExist for Windows.
-- This is case-sensitive only on the file name part, not on the directory part.
-- (Ideally, path components coming from module name components should be
--  checked case-sensitively and the other path components should be checked
--  case insenstively.)
doesFileExistCaseSensitive :: FilePath -> IO Bool
#if mingw32_HOST_OS
doesFileExistCaseSensitive f = do
  ex <- doesFileExist f
  if ex then bracket (findFirstFile f) (findClose . fst) $
               fmap (takeFileName f ==) . getFindDataFileName . snd
        else return False
#else
doesFileExistCaseSensitive f = doesFileExist f
#endif

------------------------------------------------------------------------
-- Generators

instance Arbitrary AbsolutePath where
  arbitrary = mk . take 3 . map (take 2) <$>
                listOf (listOf1 (elements "a1"))
    where mk ps = mkAbsolute (joinPath $ rootPath : ps)

------------------------------------------------------------------------
-- All tests

tests :: IO Bool
tests = runTests "Agda.Utils.FileName"
  [ quickCheck' absolutePathInvariant
  , quickCheck' prop_mkAbsolute
  ]
