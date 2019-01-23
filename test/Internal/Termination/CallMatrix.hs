{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE TemplateHaskell            #-}

module Internal.Termination.CallMatrix
  ( callMatrix
  , tests
  ) where

import Agda.Termination.CallMatrix
import Agda.Termination.CutOff
import Agda.Termination.SparseMatrix ( Size )

import Internal.Helpers
import Internal.Termination.Order ()
import Internal.Termination.SparseMatrix ( matrix )

------------------------------------------------------------------------
-- * Generators and tests
------------------------------------------------------------------------

deriving instance CoArbitrary CallMatrix

-- ** CallMatrix

instance Arbitrary CallMatrix where
  arbitrary = callMatrix =<< arbitrary

-- | Generates a call matrix of the given size.

callMatrix :: Size ArgumentIndex -> Gen CallMatrix
callMatrix sz = CallMatrix <$> matrix sz

-- ** CallMatrixAug

instance Arbitrary cinfo => Arbitrary (CallMatrixAug cinfo) where
  arbitrary = CallMatrixAug <$> arbitrary <*> arbitrary

instance CoArbitrary cinfo => CoArbitrary (CallMatrixAug cinfo) where
  coarbitrary (CallMatrixAug m info) = coarbitrary m . coarbitrary info

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
tests = testProperties "Internal.Termination.CallMatrix" $allProperties
