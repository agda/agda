
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
-- All tests

tests :: IO Bool
tests = runTests "Internal.Utils.Either"
  [ quickCheck' (prop_allRight :: [Either Integer Bool] -> Bool)
  ]
