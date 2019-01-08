{-# LANGUAGE TemplateHaskell #-}

module Internal.TypeChecking.Monad.Base ( tests ) where

import Agda.TypeChecking.Monad.Base

import Internal.Helpers

------------------------------------------------------------------------
-- Instances

instance Arbitrary Simplification where
  arbitrary = elements [ YesSimplification, NoSimplification ]

------------------------------------------------------------------------------
-- Properties

-- | 'Simplification' is a monoid.
prop_monoid_Simplification :: Property3 Simplification
prop_monoid_Simplification = isMonoid

prop_allOptionsListed :: Bool
prop_allOptionsListed = sameElements allOptions splitupOptions
  where
    allOptions = [toEnum 0..]
    splitupOptions = coInfectiveOptions ++ infectiveOptions
    sameElements xs ys = all (`elem` ys) xs && all (`elem` xs) ys

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
tests = testProperties "Internal.TypeChecking.Monad.Base" $allProperties
