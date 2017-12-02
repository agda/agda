
module InternalTests.TypeChecking.Free.Lazy () where

import Agda.TypeChecking.Free.Lazy

import InternalTests.Syntax.Common ()

import Test.QuickCheck

------------------------------------------------------------------------------
-- QuickCheck instances

instance Arbitrary FlexRig where
  arbitrary = oneof
    [ pure $ Flexible mempty -- TODO
    , pure WeaklyRigid
    , pure Unguarded
    , pure StronglyRigid
    ]

instance Arbitrary VarOcc where
  arbitrary = VarOcc <$> arbitrary <*> arbitrary
