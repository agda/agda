{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module Internal.TypeChecking.Free.Lazy () where

import Agda.TypeChecking.Free.Lazy

import Internal.Syntax.Common ()

import Test.QuickCheck

------------------------------------------------------------------------------
-- QuickCheck instances

deriving instance Arbitrary MetaSet

-- | For testing, we generate only @Flexible mempty@, since non-empty
--   'MetaSet's destroy distributivity laws, amongst others.
instance Arbitrary FlexRig where
  arbitrary = oneof
    [ pure $ Flexible mempty
        -- ALT: Flexible <$> arbitrary
        -- However: the distributivity laws break down with non-empty MetaSet.
    , pure WeaklyRigid
    , pure Unguarded
    , pure StronglyRigid
    ]

instance Arbitrary VarOcc where
  arbitrary = VarOcc <$> arbitrary <*> arbitrary

deriving instance Eq VarMap
deriving instance Arbitrary VarMap
