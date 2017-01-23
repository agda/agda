{-# LANGUAGE TemplateHaskell #-}

module InternalTests.TypeChecking.Monad.Base ( tests ) where

import Agda.TypeChecking.Monad.Base

import InternalTests.Helpers

------------------------------------------------------------------------
-- Instances

instance Arbitrary Simplification where
  arbitrary = elements [ YesSimplification, NoSimplification ]

------------------------------------------------------------------------------
-- Properties

-- | 'Simplification' is a monoid.
prop_monoid_Simplification :: Simplification -> Simplification ->
                              Simplification -> Bool
prop_monoid_Simplification = monoid

------------------------------------------------------------------------
-- Hack to make $quickCheckAll work under ghc-7.8
return []

-- All tests
tests :: IO Bool
tests = do
  putStrLn "InternalTests.TypeChecking.Monad.Base"
  $quickCheckAll
