
module Internal.Utils.Either ( tests ) where

import Agda.Utils.Either

import Internal.Helpers

------------------------------------------------------------------------------

prop_allRight :: Eq b => [Either t b] -> Bool
prop_allRight xs =
  allRight xs ==
    if all isRight xs then
      Just $ map (\ (Right x) -> x) xs
     else
      Nothing

------------------------------------------------------------------------
-- * All tests
------------------------------------------------------------------------

-- (ASR 2018-01-06) Since the property has a type signature we cannot
-- use 'allProperties' for collecting it.

tests :: TestTree
tests = testGroup "Internal.Utils.Either"
  [ testProperty "prop_allRight" (prop_allRight :: [Either Integer Bool] -> Bool)
  ]
