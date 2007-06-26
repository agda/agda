------------------------------------------------------------------------
-- | Utilities for the 'Either' type
------------------------------------------------------------------------

module Utils.Either
  ( rights
  , tests
  ) where

import Control.Arrow
import Test.QuickCheck

-- | Extracts the right elements from the list.

rights :: [Either a b] -> [b]
rights xs = [ x | Right x <- xs ]

-- | Extracts the left elements from the list.

lefts :: [Either a b] -> [a]
lefts xs = [ x | Left x <- xs ]

------------------------------------------------------------------------
-- All tests

tests :: IO ()
tests = return ()

