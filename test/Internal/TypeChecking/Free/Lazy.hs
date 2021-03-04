
module Internal.TypeChecking.Free.Lazy () where

import Agda.TypeChecking.Free.Lazy
import Agda.Utils.IntSet.Typed (IsInt, ISet)
import qualified Agda.Utils.IntSet.Typed as ISet

import Internal.Syntax.Common ()

import Test.QuickCheck

------------------------------------------------------------------------------
-- QuickCheck instances

instance (ISet.IsInt a, Arbitrary a) => Arbitrary (ISet a) where
  arbitrary = ISet.fromList <$> arbitrary
  shrink = map ISet.fromList . shrink . ISet.toList

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
