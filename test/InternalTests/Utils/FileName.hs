{-# LANGUAGE CPP #-}

module InternalTests.Utils.FileName ( tests ) where

import Agda.Utils.FileName

#if __GLASGOW_HASKELL__ <= 708
import Control.Applicative ( (<$>) )
#endif

import qualified Data.Text as Text

import InternalTests.Helpers

import System.FilePath

------------------------------------------------------------------------
-- Generators

instance Arbitrary AbsolutePath where
  arbitrary = mk . take 3 . map (take 2) <$>
                listOf (listOf1 (elements "a1"))
    where mk ps = mkAbsolute (joinPath $ rootPath : ps)

instance CoArbitrary AbsolutePath where
  coarbitrary (AbsolutePath t) = coarbitrary (Text.unpack t)

------------------------------------------------------------------------
-- Properties

-- | The paths have to be absolute, valid and normalised, without
-- trailing path separators.

absolutePathInvariant :: AbsolutePath -> Bool
absolutePathInvariant x =
  isAbsolute f &&
  isValid f &&
  f == normalise f &&
  f == dropTrailingPathSeparator f
  where f = filePath x

prop_mkAbsolute :: FilePath -> Property
prop_mkAbsolute f =
  let path = rootPath ++ f
  in  isValid path ==> absolutePathInvariant $ mkAbsolute $ path


------------------------------------------------------------------------
-- All tests

tests :: IO Bool
tests = runTests "InternalTests.Utils.FileName"
  [ quickCheck' absolutePathInvariant
  , quickCheck' prop_mkAbsolute
  ]
