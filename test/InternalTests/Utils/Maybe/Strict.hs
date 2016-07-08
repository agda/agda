{-# LANGUAGE CPP #-}

module InternalTests.Utils.Maybe.Strict () where

import Agda.Utils.Maybe.Strict

#if __GLASGOW_HASKELL__ <= 708
import Control.Applicative ( (<$>) )
#endif

import Prelude hiding ( Maybe )

import Test.QuickCheck

------------------------------------------------------------------------------
-- QuickCheck instances

instance Arbitrary a => Arbitrary (Maybe a) where
  arbitrary = toStrict <$> arbitrary
  shrink    = map toStrict . shrink . toLazy

instance CoArbitrary a => CoArbitrary (Maybe a) where
  coarbitrary = coarbitrary . toLazy

