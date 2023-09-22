{-# LANGUAGE TemplateHaskell #-}

{-# OPTIONS_GHC -Wno-missing-signatures #-}

module Internal.Syntax.Internal.Univ ( tests ) where

import Agda.Syntax.Internal.Univ

import Internal.Helpers

instance Arbitrary Univ      where arbitrary = arbitraryBoundedEnum
instance Arbitrary IsFibrant where arbitrary = arbitraryBoolean

prop_suc_preserves_fibrancy u =
  univFibrancy (univUniv u) == univFibrancy u

prop_fun_preserves_fibrancy u1 u2 =
  univFibrancy (funUniv u1 u2) == max (univFibrancy u1) (univFibrancy u2)

prop_fun_preserves_domain u1 u2 =
  univFibrancy u1 == IsFibrant ==> funUniv u1 u2 == u2

prop_domain_funUniv prop u1 u2 =
  -- If Prop is not enabled then the ui cannot be UProp.
  (prop || u1 /= UProp && u2 /= UProp)
  ==>
  maybe True (u1 ==) $ domainUniv prop (funUniv u1 u2) u2

prop_codomain_funUniv u1 u2 =
  maybe True (u2 ==) $ codomainUniv (funUniv u1 u2) u1



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
tests = testProperties "Internal.Syntax.Internal.Univ" $allProperties
