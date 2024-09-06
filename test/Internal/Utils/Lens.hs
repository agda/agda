{-# LANGUAGE TemplateHaskell #-}

module Internal.Utils.Lens ( tests ) where

import Control.Monad.State

import Agda.Utils.Lens

import Internal.Helpers

------------------------------------------------------------------------------
-- Properties

-- Bug discovered in https://github.com/agda/agda/pull/7470#discussion_r1747232483
prop_effectfully_modify :: (Eq a, Eq b) => a -> b -> a -> b -> Bool
prop_effectfully_modify x0 y0 x1 y1 = execState p (x0, y0) == (x1, y1)
  where
    -- The change to @lSnd@ should not get lost by the use of @%==@.
    p = lFst %== \ _ -> do
          lSnd .= y1
          return x1

prop_effectfully_modify_and_value :: (Eq a, Eq b, Eq c) => a -> b -> a -> b -> c -> Bool
prop_effectfully_modify_and_value x0 y0 x1 y1 z = runState p (x0, y0) == (z, (x1, y1))
  where
    -- The change to @lSnd@ should not get lost by the use of @%%=@.
    p = lFst %%= \ _ -> do
          lSnd .= y1
          return (x1, z)


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
tests = testProperties "Internal.Utils.Lens" $allProperties
