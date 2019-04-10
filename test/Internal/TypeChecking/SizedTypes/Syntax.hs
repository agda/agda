
module Internal.TypeChecking.SizedTypes.Syntax () where

import Agda.TypeChecking.SizedTypes.Syntax

import Test.QuickCheck

------------------------------------------------------------------------------
-- QuickCheck instances

instance Arbitrary Offset where
  arbitrary = do
    NonNegative x <- arbitrary :: Gen (NonNegative Int)
    return (O x)

  shrink (O x) = map O $ filter (>= 0) (shrink x)

instance Arbitrary Cmp where
  arbitrary = arbitraryBoundedEnum

