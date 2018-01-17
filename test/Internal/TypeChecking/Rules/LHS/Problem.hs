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
tests = testProperties "Internal.TypeChecking.Rules.LHS.Problem" $allProperties
