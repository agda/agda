{-# LANGUAGE TemplateHaskell #-}

module Internal.Version ( tests ) where

import Agda.VersionCommit

import Internal.Helpers

prop_isReleaseTag :: Bool
prop_isReleaseTag = all isReleaseTag
  [ "v2.9.0"
  , "v2.8.0-rc1"
  , "v2.7.20250701"
  , "v2.6.4.3"
  , "v2.6.4.2-rc1"
  , "v2.6.4.0.20231111"
  ]

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
tests = testProperties "Internal.Version" $allProperties
