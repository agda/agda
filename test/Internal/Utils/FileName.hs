{-# LANGUAGE CPP             #-}
{-# LANGUAGE TemplateHaskell #-}

module Internal.Utils.FileName (rootPath, tests) where

import qualified Data.Text as Text
import System.FilePath

import Internal.Helpers

import Agda.Utils.FileName

------------------------------------------------------------------------
-- Helpers

rootPath :: FilePath
#ifdef mingw32_HOST_OS
rootPath = joinDrive "C:" [pathSeparator]
#else
rootPath = [pathSeparator]
#endif

------------------------------------------------------------------------
-- Generators

-- Relative paths

newtype RelativePath = RelativePath { theRelativePath :: FilePath }
  deriving (Eq, Show)

instance Arbitrary RelativePath where
  arbitrary = RelativePath . joinPath . take 3 . map (take 2) <$>
                listOf (listOf1 (elements "a1"))
    where mk ps = mkAbsolute (joinPath $ rootPath : ps)

instance CoArbitrary RelativePath where
  coarbitrary (RelativePath p) = coarbitrary p

-- Absolute paths

instance Arbitrary AbsolutePath where
  arbitrary = mkAbsolute . (rootPath </>) . theRelativePath  <$> arbitrary

instance CoArbitrary AbsolutePath where
  coarbitrary (AbsolutePath t) = coarbitrary (Text.unpack t)

------------------------------------------------------------------------
-- Properties

-- | The paths have to be absolute, valid and normalised, without
-- trailing path separators.

prop_absolutePathInvariant :: AbsolutePath -> Bool
prop_absolutePathInvariant x =
  isAbsolute f &&
  isValid f &&
  f == normalise f &&
  f == dropTrailingPathSeparator f
  where f = filePath x

prop_mkAbsolute :: FilePath -> Property
prop_mkAbsolute f =
  let path = rootPath ++ f
  in  isValid path ==> prop_absolutePathInvariant $ mkAbsolute $ path

-- | @`'relativizeAbsolutePath'` root@ inverts @(root '</>')@.
prop_relativize_inverts_combine :: AbsolutePath -> RelativePath -> Bool
prop_relativize_inverts_combine root (RelativePath rest) =
  let path = mkAbsolute $ filePath root </> rest
  in  relativizeAbsolutePath path root == Just (if null rest then "." else rest)

------------------------------------------------------------------------
-- * All tests
------------------------------------------------------------------------

-- Template Haskell hack to make the following $allProperties work
-- under ghc-7.8.
return [] -- KEEP!

-- | All tests as collected by 'allProperties'.
--
-- Using 'allProperties' is convenient and superior to the manual
-- enumeration of tests, since the name of the property is added
-- automatically.

tests :: TestTree
tests = testProperties "Internal.Utils.FileName" $allProperties
