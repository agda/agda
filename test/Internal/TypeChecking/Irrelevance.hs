{-# LANGUAGE TemplateHaskell #-}

module Internal.TypeChecking.Irrelevance ( tests ) where

import Agda.Syntax.Common
import Agda.TypeChecking.Irrelevance

import Internal.Helpers
import Internal.Syntax.Common ()

------------------------------------------------------------------------
-- * Tests
------------------------------------------------------------------------

prop_galois :: Relevance -> Relevance -> Relevance -> Bool
prop_galois r x y =
  x `moreRelevant` (r `composeRelevance` y) ==
  (r `inverseComposeRelevance` x) `moreRelevant` y

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
tests = testProperties "Internal.TypeChecking.Irrelevance" $allProperties
