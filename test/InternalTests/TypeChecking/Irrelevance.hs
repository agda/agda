{-# LANGUAGE TemplateHaskell #-}

module InternalTests.TypeChecking.Irrelevance ( tests ) where

import Agda.Syntax.Common
import Agda.TypeChecking.Irrelevance

import InternalTests.Helpers
import InternalTests.Syntax.Common ()

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

-- Template Haskell hack to make the following $quickCheckAll work
-- under ghc-7.8.
return [] -- KEEP!

-- | All tests as collected by 'quickCheckAll'.

tests :: IO Bool
tests = do
  putStrLn "InternalTests.TypeChecking.Irrelevance"
  $quickCheckAll
