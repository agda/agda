
module Internal.TypeChecking.Free.Lazy () where

import Agda.TypeChecking.Free.Lazy

import qualified Data.HashSet as HashSet

import Internal.Syntax.Common ()

import Test.QuickCheck

------------------------------------------------------------------------------
-- QuickCheck instances

instance Arbitrary MetaSet where
  arbitrary = MetaSet . HashSet.fromList <$> arbitrary

-- | For testing, we generate only @Flexible mempty@, since non-empty
--   'MetaSet's destroy distributivity laws, amongst others.
instance Arbitrary a => Arbitrary (FlexRig' a) where
  arbitrary = oneof
    [ Flexible <$> arbitrary
        -- Note that the distributivity laws may break down with non-empty MetaSet.
    , pure WeaklyRigid
    , pure Unguarded
    , pure StronglyRigid
    ]

instance Arbitrary a => Arbitrary (VarOcc' a) where
  arbitrary = VarOcc <$> arbitrary <*> arbitrary

deriving instance Arbitrary a => Arbitrary (VarMap' a)
