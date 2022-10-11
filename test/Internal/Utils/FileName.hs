{-# LANGUAGE CPP             #-}
{-# LANGUAGE TemplateHaskell #-}

module Internal.Utils.FileName (tests) where

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

instance Arbitrary Path where
  arbitrary = mk . take 3 . map (take 2) <$>
                listOf (listOf1 (elements "a1"))
    where mk ps = mkPath (joinPath ps)

instance CoArbitrary Path where
  coarbitrary (Path t) = coarbitrary (Text.unpack t)

-- | Absolute paths.

absolutePath :: Gen Path
absolutePath = mkPath . (rootPath </>) . filePath <$> arbitrary

------------------------------------------------------------------------
-- Properties

-- | The paths have to be valid and normalised, without
-- trailing path separators.

prop_pathInvariant :: Path -> Bool
prop_pathInvariant x =
  isValid f &&
  f == normalise f &&
  f == dropTrailingPathSeparator f
  where f = filePath x

prop_mkPath :: FilePath -> Property
prop_mkPath path =
  isValid path ==> prop_pathInvariant (mkPath path)

-- | @`'relativizeAbsolutePath'` root@ inverts @(root '</>')@.
prop_relativize_inverts_combine :: Path -> Property
prop_relativize_inverts_combine rest' =
  forAll absolutePath $ \root ->
  let path = mkPath $ filePath root </> rest in
  relativizeAbsolutePath path root ==
  Just (if null rest then "." else rest)
  where rest = filePath rest'

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
