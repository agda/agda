{-# LANGUAGE TemplateHaskell #-}

module Internal.Syntax.Internal ( tests ) where

import Agda.Syntax.Internal
import Agda.TypeChecking.Substitute ()

import Internal.Helpers
import Internal.Syntax.Common ()

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
tests = testProperties "Internal.Syntax.Internal" $allProperties
