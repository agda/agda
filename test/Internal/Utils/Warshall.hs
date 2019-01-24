{-# LANGUAGE TemplateHaskell #-}

module Internal.Utils.Warshall ( tests ) where

import Internal.Helpers

-- Testing ----------------------------------------------------------------

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
tests = testProperties "Internal.Utils.Warshall" $allProperties

