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

-- Template Haskell hack to make the following $quickCheckAll work
-- under ghc-7.8.
return [] -- KEEP!

-- | All tests as collected by 'quickCheckAll'.

tests :: IO Bool
tests = do
  putStrLn "Internal.Interaction.Highlighting.Precise"
  $quickCheckAll
