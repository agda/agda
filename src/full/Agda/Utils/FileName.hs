{-# LANGUAGE CPP, DeriveDataTypeable #-}

{-| Operations on file names. -}
module Agda.Utils.FileName
  ( AbsolutePath
  , filePath
  , mkAbsolute
  , absolute
  , (===)
  , tests
  ) where

import Agda.Utils.TestHelpers
import Agda.Utils.QuickCheck
import Data.Function
import Data.Generics
import Data.List
import Data.Maybe
import Control.Applicative
import Control.Monad
import System.Directory
import System.FilePath

#include "../undefined.h"
import Agda.Utils.Impossible

-- | Paths which are known to be absolute.
--
-- Note that the 'Eq' and 'Ord' instances do not check if different
-- paths point to the same files or directories.

newtype AbsolutePath = AbsolutePath { filePath :: FilePath }
  deriving (Show, Eq, Ord, Typeable, Data)

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
  absolutePathInvariant $ mkAbsolute (pathSeparator : f)

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

------------------------------------------------------------------------
-- Generators

instance Arbitrary AbsolutePath where
  arbitrary = mk . take 3 . map (take 2) <$>
                listOf (listOf1 (elements "a1"))
    where mk ps = AbsolutePath (joinPath $ [pathSeparator] : ps)

------------------------------------------------------------------------
-- All tests

tests = runTests "Agda.Utils.FileName"
  [ quickCheck' absolutePathInvariant
  , quickCheck' prop_mkAbsolute
  ]
