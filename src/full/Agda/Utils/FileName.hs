{-# LANGUAGE CPP, DeriveDataTypeable #-}

{-| Operations on file names. -}
module Agda.Utils.FileName
  ( AbsolutePath
  , filePath
  , mkAbsolute
  , absolute
  , (===)
  , doesFileExistCaseSensitive
  , tests
  ) where

import Agda.Utils.TestHelpers
import Agda.Utils.QuickCheck
import Data.Function
import Data.Typeable (Typeable)
import Data.List
import Data.Maybe
import Control.Applicative
import Control.Monad
import System.Directory
import System.FilePath

#if mingw32_HOST_OS
import Control.Exception (bracket)
import System.Win32 (findFirstFile, findClose, getFindDataFileName)
#endif

#include "../undefined.h"
import Agda.Utils.Impossible

-- | Paths which are known to be absolute.
--
-- Note that the 'Eq' and 'Ord' instances do not check if different
-- paths point to the same files or directories.

newtype AbsolutePath = AbsolutePath { filePath :: FilePath }
  deriving (Eq, Ord, Typeable)

instance Show AbsolutePath where
  show = filePath

-- | The paths have to be absolute, valid and normalised, without
-- trailing path separators.

absolutePathInvariant :: AbsolutePath -> Bool
absolutePathInvariant (AbsolutePath f) =
  isAbsolute f &&
  isValid f &&
  f == normalise f &&
  f == dropTrailingPathSeparator f

-- | Constructs 'AbsolutePath's.
--
-- Precondition: The path must be absolute and valid.

mkAbsolute :: FilePath -> AbsolutePath
mkAbsolute f
  | isAbsolute f =
      AbsolutePath $ dropTrailingPathSeparator $ normalise f
  | otherwise    = __IMPOSSIBLE__

prop_mkAbsolute f =
  let path = rootPath ++ f
  in
#if mingw32_HOST_OS
      isValid path ==>
#endif
      absolutePathInvariant $ mkAbsolute $ path

#if mingw32_HOST_OS
rootPath = joinDrive "C:" [pathSeparator]
#else
rootPath = [pathSeparator]
#endif

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

tests = runTests "Agda.Utils.FileName"
  [ quickCheck' absolutePathInvariant
  , quickCheck' prop_mkAbsolute
  ]
