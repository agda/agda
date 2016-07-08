
module InternalTests.Syntax.Common () where

import Agda.Syntax.Common

import Test.QuickCheck

------------------------------------------------------------------------------
-- QuickCheck instances

instance Arbitrary Relevance where
  arbitrary = elements allRelevances

instance Arbitrary NameId where
  arbitrary = elements [ NameId x y | x <- [-1, 1], y <- [-1, 1] ]

instance CoArbitrary NameId

instance Arbitrary Induction where
  arbitrary = elements [Inductive, CoInductive]

instance CoArbitrary Induction where
  coarbitrary Inductive   = variant 0
  coarbitrary CoInductive = variant 1

