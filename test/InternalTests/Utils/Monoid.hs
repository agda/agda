{-# LANGUAGE TemplateHaskell #-}

module InternalTests.Utils.Monoid ( tests ) where

import Agda.Utils.Monoid

import InternalTests.Helpers

------------------------------------------------------------------------
-- Instances

instance Arbitrary MaxNat where
  arbitrary = do
    NonNegative x <- arbitrary
    return x

------------------------------------------------------------------------------
-- Properties

-- | 'MaxNat' is a monoid.
prop_monoid_MaxNat :: MaxNat -> MaxNat -> MaxNat -> Bool
prop_monoid_MaxNat = monoid

------------------------------------------------------------------------
-- Hack to make $quickCheckAll work under ghc-7.8
return []

-- All tests
tests :: IO Bool
tests = do
  putStrLn "InternalTests.Utils.Monoid"
  $quickCheckAll
