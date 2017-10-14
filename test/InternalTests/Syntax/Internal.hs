{-# LANGUAGE CPP             #-}
{-# LANGUAGE TemplateHaskell #-}

module InternalTests.Syntax.Internal ( tests ) where

import Agda.Syntax.Internal
import Agda.TypeChecking.Substitute ()

import InternalTests.Helpers
import InternalTests.Syntax.Common ()

------------------------------------------------------------------------
-- Instances

instance Arbitrary NotBlocked where
  arbitrary = elements [ Underapplied
                       , AbsurdMatch
                       , MissingClauses
                       , ReallyNotBlocked
                       -- , StuckOn Elim  -- TODO
                       ]

instance Arbitrary (Blocked ()) where
  arbitrary = do
    m  <- arbitrary
    bs <- arbitrary
    elements [ Blocked m (), NotBlocked bs () ]

------------------------------------------------------------------------------
-- Properties

-- | 'NotBlocked' is a monoid.
prop_monoid_NotBlocked :: Property3 NotBlocked
prop_monoid_NotBlocked = isMonoid

-- | 'Blocked_' is a monoid.
prop_monoid_Blocked_ :: Property3 Blocked_
prop_monoid_Blocked_ = isMonoid

------------------------------------------------------------------------
-- Hack to make $quickCheckAll work under ghc-7.8
return []

-- All tests
tests :: IO Bool
tests = do
  putStrLn "InternalTests.Syntax.Internal"
  $quickCheckAll
