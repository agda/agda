{-# LANGUAGE CPP             #-}
{-# LANGUAGE TemplateHaskell #-}

module InternalTests.Syntax.Internal ( tests ) where

import Agda.Syntax.Internal

import InternalTests.Helpers
import InternalTests.Syntax.Common ()

------------------------------------------------------------------------
-- Instances

-- ASR (2017-01-23). Hack!

-- Why GHC <= 7.8.4 generate the error

--   test/InternalTests/Syntax/Internal.hs:18:10:
--       Duplicate instance declarations:
--         instance [overlap ok] Eq NotBlocked
--           -- Defined at test/InternalTests/Syntax/Internal.hs:18:10
--         instance [overlap ok] Eq NotBlocked
--           -- Defined in ‘Agda.TypeChecking.Substitute’

-- if Agda.TypeChecking.Substitute is not imported?

#if __GLASGOW_HASKELL__ > 708
instance Eq NotBlocked where
  StuckOn _        == StuckOn _        = True  -- FIXME
  Underapplied     == Underapplied     = True
  AbsurdMatch      == AbsurdMatch      = True
  MissingClauses   == MissingClauses   = True
  ReallyNotBlocked == ReallyNotBlocked = True
  _                == _                = False
#endif

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
prop_monoid_NotBlocked = isMonoid

-- | 'Blocked_' is a monoid.
prop_monoid_Blocked_ :: Blocked_ -> Blocked_ -> Blocked_ -> Bool
prop_monoid_Blocked_ = isMonoid

------------------------------------------------------------------------
-- Hack to make $quickCheckAll work under ghc-7.8
return []

-- All tests
tests :: IO Bool
tests = do
  putStrLn "InternalTests.Syntax.Internal"
  $quickCheckAll
