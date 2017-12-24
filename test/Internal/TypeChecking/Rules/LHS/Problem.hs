{-# LANGUAGE TemplateHaskell #-}

module Internal.TypeChecking.Rules.LHS.Problem ( tests ) where

import Agda.TypeChecking.Rules.LHS.Problem

import Internal.Helpers

------------------------------------------------------------------------
-- Instances

instance Arbitrary FlexChoice where
  arbitrary = elements [ ChooseLeft, ChooseRight, ChooseEither, ExpandBoth ]

------------------------------------------------------------------------------
-- Properties

-- | 'FlexChoice' is a monoid.
prop_monoid_FlexChoice :: Property3 FlexChoice
prop_monoid_FlexChoice = isMonoid

------------------------------------------------------------------------
-- Hack to make $quickCheckAll work under ghc-7.8
return []

-- All tests
tests :: IO Bool
tests = do
  putStrLn "Internal.TypeChecking.Rules.LHS.Problem"
  $quickCheckAll
