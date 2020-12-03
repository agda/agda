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

-- RETIRED:  LONG OUTDATED call matrix invariant

-- -- | In a call matrix at most one element per row may be different
-- -- from 'unknown'.

-- callMatrixInvariant :: CallMatrix -> Bool
-- callMatrixInvariant (CallMatrix m) =
--   matrixInvariant m &&
--   all ((<= 1) . length . filter (/= unknown)) (toLists m)

-- prop_Arbitrary_CallMatrix = callMatrixInvariant

-- -- | Generates a call matrix of the given size.

-- callMatrix :: Size ArgumentIndex -> Gen CallMatrix
-- callMatrix sz = do
--   m <- matrixUsingRowGen sz rowGen
--   return $ CallMatrix { mat = m }
--   where
--   rowGen :: ArgumentIndex -> Gen [Order]
--   rowGen 0 = return []
--   rowGen n = do
--     x <- arbitrary
--     i <- choose (0, n - 1)
--     return $ genericReplicate i unknown ++ [x] ++
--              genericReplicate (n - 1 - i) unknown

-- prop_callMatrix sz =
--   forAll (callMatrix sz) $ \cm ->
--     callMatrixInvariant cm
--     &&
--     size (mat cm) == sz

-- prop_cmMul sz =
--   forAll natural $ \c2 ->
--   forAll (callMatrix sz) $ \cm1 ->
--   forAll (callMatrix $ Size { rows = cols sz, cols = c2 }) $ \cm2 ->
--     callMatrixInvariant (cm1 >*< cm2)

-- tests :: IO Bool
-- tests = runTests "Agda.Termination.CallMatrix"
--   [ quickCheck' callMatrixInvariant
--   , quickCheck' prop_Arbitrary_CallMatrix
--   , quickCheck' prop_callMatrix
--   , quickCheck' prop_cmMul
--   ]
--   where ?cutoff = DontCutOff -- CutOff 2  -- don't cut off in tests!
