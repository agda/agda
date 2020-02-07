{-# LANGUAGE TemplateHaskell #-}

module Internal.Utils.FileName ( tests ) where

import Agda.Utils.FileName

import qualified Data.Text as Text

import Internal.Helpers

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
