
module InternalTests.TypeChecking.Irrelevance ( tests ) where

import Agda.Syntax.Common
import Agda.TypeChecking.Irrelevance

import InternalTests.Helpers
import InternalTests.Syntax.Common

------------------------------------------------------------------------
-- * Tests
------------------------------------------------------------------------

prop_galois :: Relevance -> Relevance -> Relevance -> Bool
prop_galois r x y =
  x `moreRelevant` (r `composeRelevance` y) ==
  (r `inverseComposeRelevance` x) `moreRelevant` y

tests :: IO Bool
tests = runTests "InternalTests.TypeChecking.Irrelevance"
  [ quickCheck' prop_galois
  ]
