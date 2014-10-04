{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE ScopedTypeVariables       #-}
{-# LANGUAGE TemplateHaskell           #-}

module Agda.TypeChecking.SizedTypes.Tests where

import Control.Applicative

import Test.QuickCheck
import Test.QuickCheck.All

import Agda.TypeChecking.SizedTypes.Syntax
import Agda.TypeChecking.SizedTypes.WarshallSolver
import Agda.TypeChecking.SizedTypes.Utils

instance Arbitrary Cmp where
  arbitrary = arbitraryBoundedEnum

instance Arbitrary Weight where
  arbitrary = frequency
    [ (1, return Infinity)
    , (5, Offset <$> choose (0, 200))
    ]

-- instance Arbitrary Label where
--   arbitrary = Label <$> arbitrary <*> arbitrary
instance Arbitrary Label where
  arbitrary = frequency
    [ (1, return LInf)
    , (5, Label <$> arbitrary <*> arbitrary)
    ]

-- * Label interpretation

type Relation a = a -> a -> Bool

class AsWeightRelation b where
  eval :: b -> Relation Weight

instance AsWeightRelation Cmp where
  eval Le = (<=)
  eval Lt = (<)

instance AsWeightRelation Label where
  eval (Label cmp w) x y = eval cmp x (y `plus` w)
  eval LInf          _ _ = True

prop_MeetSound (l :: Label) l' x y =
  eval l x y && eval l' x y ==> eval (meet l l') x y

prop_MeetComplete (l :: Label) l' x y =
  eval (meet l l') x y ==> eval l x y && eval l' x y

prop_ComposeSound (l1 :: Label) l2 x y z =
  eval l1 x y && eval l2 y z ==> eval (compose l1 l2) x z

prop_ComposeComplete (l1 :: Label) l2 k z = let x = Offset k in
  eval (compose l1 l2) x z ==>
    let y = z + toWeight l2
    in  eval l1 x y -- && eval l2 y z -- does not hold for l2 = \infty
    -- Andreas, 2014-05-20, Issue 1134
    -- If we replace the \infty with its unicode, issue 1134 is triggered:
    -- "... GHC 7.6.3 and quickcheck 2.6.
    -- It turns out that for some reason Gentoo eclass unsets locale
    -- to POSIX when building haskell packages. So the issue is easy
    -- to reproduce with `LANG=POSIX ./setup build`."
    --
    -- Funnily, the offending unicode symbol is in a comment.
    -- Some issue for TemplateHaskell / QuickCheck.

-- * Generic properties

propCommutative o x y   = x `o` y == y `o` x
propAssociative o x y z = x `o` (y `o` z) == (x `o` y) `o` z
propIdempotent  o x     = (x `o` x) == x
propUnit        o u x   = u `o` x == x && x `o` u == x
propZero        o z x   = z `o` x == z && x `o` z == z
propDistL       o p x y z = x `o` (y `p` z) == (x `o` y) `p` (x `o` z)
propDistR       o p x y z = (x `p` y) `o` z == (x `o` z) `p` (y `o` z)
propDistributive o p x y z = propDistL o p x y z && propDistR o p x y z

propSemiLattice o x y z = propCommutative o x y && propAssociative o x y z && propIdempotent o x
propBoundedSemiLattice o u x y z = propSemiLattice o x y z && propUnit o u x
propMonoid o u x y z    = propAssociative o x y z && propUnit o u x
propDioid p n o u x y z = propBoundedSemiLattice p n x y z
                       && propMonoid o u x y z
                       && propDistributive o p x y z
                       && propZero o n x

-- | Properties of 'Dioid' class.
propDioid_Gen = propDioid meet top compose unitCompose

-- | @Weight@ instance.
prop_Dioid_Weight x y z = propDioid_Gen (x :: Weight) y z

-- | @Label@ instance.
prop_SemiLattice_Label x y z = propSemiLattice meet (x :: Label) y z
prop_Unit_Label x  = propUnit meet top (x :: Label)
prop_BoundedSemiLattice_Label x y z = propBoundedSemiLattice meet top (x :: Label) y z
prop_Monoid_Label x y z = propMonoid compose unitCompose (x :: Label) y z
prop_DistL_Label x y z = propDistL compose meet (x :: Label) y z
prop_DistR_Label x y z = propDistR compose meet (x :: Label) y z
prop_Dist_Label x y z = propDistributive compose meet (x :: Label) y z
prop_Zero_Label x     = propZero compose top (x :: Label)
prop_Dioid_Label x y z = propDioid_Gen (x :: Label) y z

------------------------------------------------------------------------
-- * All tests
------------------------------------------------------------------------

-- Template Haskell hack to make the following $quickCheckAll work
-- under ghc-7.8.
return [] -- KEEP!

-- | Runs all tests starting with "prop_" in this file.
tests :: IO Bool
tests = do
  putStrLn "Agda.TypeChecking.SizedTypes.Tests"
  $quickCheckAll
