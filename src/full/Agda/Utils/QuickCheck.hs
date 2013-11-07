
module Agda.Utils.QuickCheck
  ( module Test.QuickCheck
  , module Agda.Utils.QuickCheck
  ) where

import Test.QuickCheck

isSuccess :: Result -> Bool
isSuccess Success{} = True
isSuccess _         = False

quickCheck' :: Testable prop => prop -> IO Bool
quickCheck' p = fmap isSuccess $ quickCheckResult p

quickCheckWith' :: Testable prop => Args -> prop -> IO Bool
quickCheckWith' args p = fmap isSuccess $ quickCheckWithResult args p
