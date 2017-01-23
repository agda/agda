{-# LANGUAGE TemplateHaskell #-}

module InternalTests.TypeChecking.Rules.LHS.Problem ( tests ) where

import Agda.TypeChecking.Rules.LHS.Problem

import InternalTests.Helpers

------------------------------------------------------------------------
-- Instances

instance Arbitrary FlexChoice where
  arbitrary = elements [ ChooseLeft, ChooseRight, ChooseEither, ExpandBoth ]

------------------------------------------------------------------------------
-- Properties

-- | 'FlexChoice' is a monoid.
prop_monoid_FlexChoice :: FlexChoice -> FlexChoice -> FlexChoice -> Bool
prop_monoid_FlexChoice = monoid

------------------------------------------------------------------------
-- Hack to make $quickCheckAll work under ghc-7.8
return []

-- All tests
tests :: IO Bool
tests = do
  putStrLn "InternalTests.TypeChecking.Rules.LHS.Problem"
  $quickCheckAll
