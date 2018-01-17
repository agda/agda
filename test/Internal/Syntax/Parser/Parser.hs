{-# LANGUAGE TemplateHaskell #-}

module Internal.Syntax.Parser.Parser ( tests ) where

import Agda.Syntax.Parser.Parser

import Internal.Helpers

------------------------------------------------------------------------------

prop_splitOnDots :: Bool
prop_splitOnDots = and
  [ splitOnDots ""         == [""]
  , splitOnDots "foo.bar"  == ["foo", "bar"]
  , splitOnDots ".foo.bar" == ["", "foo", "bar"]
  , splitOnDots "foo.bar." == ["foo", "bar", ""]
  , splitOnDots "foo..bar" == ["foo", "", "bar"]
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
tests = testProperties "Internal.Syntax.Parser.Parser" $allProperties
