{-# LANGUAGE TemplateHaskell #-}

module InternalTests.Syntax.Internal ( tests ) where

import Agda.Syntax.Internal

import InternalTests.Helpers
import InternalTests.Syntax.Common ()

------------------------------------------------------------------------
-- Instances

instance Eq NotBlocked where
  StuckOn _        == StuckOn _        = True  -- FIXME
  Underapplied     == Underapplied     = True
  AbsurdMatch      == AbsurdMatch      = True
  MissingClauses   == MissingClauses   = True
  ReallyNotBlocked == ReallyNotBlocked = True
  _                == _                = False

instance Arbitrary NotBlocked where
  arbitrary = elements [ Underapplied
                       , AbsurdMatch
                       , MissingClauses
                       , ReallyNotBlocked
                       -- , StuckOn Elim  -- TODO
                       ]

instance Eq (Blocked ()) where
  Blocked m _     == Blocked m' _     = m == m'
  NotBlocked bs _ == NotBlocked bs' _ = bs == bs'
  _               == _                = False

instance Arbitrary (Blocked ()) where
  arbitrary = do
    m  <- arbitrary
    bs <- arbitrary
    elements [ Blocked m (), NotBlocked bs () ]

------------------------------------------------------------------------------
-- Properties

-- | 'NotBlocked' is a monoid.
prop_monoid_NotBlocked :: NotBlocked -> NotBlocked -> NotBlocked -> Bool
prop_monoid_NotBlocked = monoid

-- | 'Blocked_' is a monoid.
prop_monoid_Blocked_ :: Blocked_ -> Blocked_ -> Blocked_ -> Bool
prop_monoid_Blocked_ = monoid

------------------------------------------------------------------------
-- Hack to make $quickCheckAll work under ghc-7.8
return []

-- All tests
tests :: IO Bool
tests = do
  putStrLn "InternalTests.Syntax.Internal"
  $quickCheckAll
