------------------------------------------------------------------------
-- Equality and ordering for indexed types
------------------------------------------------------------------------

{-# LANGUAGE GADTs, FlexibleInstances #-}

module IndexedOrd
  ( Equal(..)
  , boolToEq
  , eqToBool
  , IndexedEq(..)
  , IndexedOrd(..)
  ) where

import Test.QuickCheck

-- | Provable type equality.

data Equal i j where
  Refl :: Equal i i

-- | @boolToEq@ converts 'True' to @'Just' 'Refl'@ and 'False' to
-- 'Nothing'.

boolToEq :: Bool -> Maybe (Equal i i)
boolToEq False = Nothing
boolToEq True  = Just Refl

-- | @eqToBool@ is the inverse of 'boolToEq'.

eqToBool :: Maybe (Equal i j) -> Bool
eqToBool Nothing     = False
eqToBool (Just Refl) = True

prop_eqToEq     meq = boolToEq (eqToBool meq) == meq
prop_boolToBool b   = eqToBool (boolToEq b)   == b

-- | A variant of 'Eq' for indexed types.

class IndexedEq t where
  iEq :: t i -> t j -> Maybe (Equal i j)

-- | A variant of 'Ord' for indexed types.

class IndexedEq t => IndexedOrd t where
  iCompare :: t i -> t j -> Ordering

------------------------------------------------------------------------
-- Some instances for Equal

instance Eq (Equal i j) where
  _ == _ = True

instance Ord (Equal i j) where
  compare _ _ = EQ

instance Show (Equal i j) where
  show _ = "Refl"

instance Arbitrary (Equal i i) where
  arbitrary = return Refl

instance CoArbitrary (Equal i j) where
  coarbitrary Refl = id

------------------------------------------------------------------------
-- All the test cases above

tests = do
  quickCheck prop_boolToBool
  quickCheck prop_eqToEq
