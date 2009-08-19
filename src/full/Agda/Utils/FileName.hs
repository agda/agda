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
-- Precondition: The path must be absolute.

mkAbsolute :: FilePath -> AbsolutePath
mkAbsolute f
  | isAbsolute f =
      AbsolutePath $ dropTrailingPathSeparator $ normalise f
  | otherwise    = __IMPOSSIBLE__

prop_mkAbsolute f =
  absolutePathInvariant $ mkAbsolute (pathSeparator : f)

-- | Makes the path absolute.
--
-- This function raises an @__IMPOSSIBLE__@ error if
-- 'canonicalizePath' does not return an absolute path.

absolute :: FilePath -> IO AbsolutePath
absolute f = mkAbsolute <$> canonicalizePath f

-- | Tries to establish if the two file paths point to the same file
-- (or directory).

infix 4 ===

(===) :: FilePath -> FilePath -> IO Bool
p1 === p2 = do
  p1 <- canonicalizePath p1
  p2 <- canonicalizePath p2
  return $ equalFilePath p1 p2

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
