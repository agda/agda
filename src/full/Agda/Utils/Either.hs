------------------------------------------------------------------------
-- | Utilities for the 'Either' type
------------------------------------------------------------------------

module Agda.Utils.Either
  ( isLeft, isRight
  , tests
  ) where

import Control.Arrow
import Agda.Utils.TestHelpers

-- | Returns 'True' iff the argument is @'Right' x@ for some @x@.

isRight :: Either a b -> Bool
isRight (Right _) = True
isRight (Left  _) = False

-- | Returns 'True' iff the argument is @'Left' x@ for some @x@.

isLeft :: Either a b -> Bool
isLeft (Right _) = False
isLeft (Left _)  = True

------------------------------------------------------------------------
-- All tests

tests :: IO Bool
tests = runTests "Agda.Utils.Either" []
