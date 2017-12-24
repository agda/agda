{-# LANGUAGE TemplateHaskell #-}

module InternalTests.Syntax.Parser.Parser ( tests ) where

import Agda.Syntax.Parser.Parser

import InternalTests.Helpers

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

-- Template Haskell hack to make the following $quickCheckAll work
-- under ghc-7.8.
return [] -- KEEP!

-- | All tests as collected by 'quickCheckAll'.

tests :: IO Bool
tests = do
  putStrLn "InternalTests.Interaction.Highlighting.Precise"
  $quickCheckAll
