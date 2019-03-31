{-# LANGUAGE TemplateHaskell #-}

module Internal.TypeChecking.SizedTypes ( tests ) where

import Agda.TypeChecking.SizedTypes.Syntax ( Cmp(Le, Lt), Offset )

import Agda.TypeChecking.SizedTypes.WarshallSolver
  ( Label(Label,LInf)
  , Weight(Offset)
  , toWeight
  )

import Agda.TypeChecking.SizedTypes.Utils
  ( Dioid(compose, unitCompose)
  , MeetSemiLattice(meet)
  , Plus(plus)
  , Top(top)
  )

import Internal.Helpers
import Internal.TypeChecking.SizedTypes.WarshallSolver ()

------------------------------------------------------------------------------

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

prop_MeetSound :: Label -> Label -> Weight -> Weight -> Property
prop_MeetSound l l' x y =
  eval l x y && eval l' x y ==> eval (meet l l') x y

prop_MeetComplete :: Label -> Label -> Weight -> Weight -> Property
prop_MeetComplete l l' x y =
  eval (meet l l') x y ==> eval l x y && eval l' x y

prop_ComposeSound :: Label -> Label -> Weight -> Weight -> Weight -> Property
prop_ComposeSound l1 l2 x y z =
  eval l1 x y && eval l2 y z ==> eval (compose l1 l2) x z

prop_ComposeComplete :: Label -> Label -> Offset -> Weight -> Property
prop_ComposeComplete l1 l2 k z = let x = Offset k in
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

propCommutative :: Eq b => (a -> a -> b) -> a -> a -> Bool
propCommutative o x y = x `o` y == y `o` x

propAssociative :: Eq a => (a -> a -> a) -> a -> a -> a -> Bool
propAssociative o x y z = x `o` (y `o` z) == (x `o` y) `o` z

propIdempotent :: Eq a => (a -> a -> a) -> a -> Bool
propIdempotent o x = (x `o` x) == x

propUnit :: Eq a => (a -> a -> a) -> a -> a -> Bool
propUnit o u x = u `o` x == x && x `o` u == x

propZero :: Eq a => (a -> a -> a) -> a -> a -> Bool
propZero o z x = z `o` x == z && x `o` z == z

propDistL :: Eq b => (a -> b -> b) -> (b -> b -> b) -> a -> b -> b -> Bool
propDistL o p x y z = x `o` (y `p` z) == (x `o` y) `p` (x `o` z)

propDistR :: Eq a => (a -> b -> a) -> (a -> a -> a) -> a -> a -> b -> Bool
propDistR o p x y z = (x `p` y) `o` z == (x `o` z) `p` (y `o` z)

propDistributive :: Eq a =>
                    (a -> a -> a) -> (a -> a -> a) -> a -> a -> a -> Bool
propDistributive o p x y z = propDistL o p x y z && propDistR o p x y z

propSemiLattice :: Eq a => (a -> a -> a) -> a -> a -> a -> Bool
propSemiLattice o x y z =
  propCommutative o x y && propAssociative o x y z && propIdempotent o x

propBoundedSemiLattice :: Eq a => (a -> a -> a) -> a -> a -> a -> a -> Bool
propBoundedSemiLattice o u x y z = propSemiLattice o x y z && propUnit o u x

propMonoid :: Eq a => (a -> a -> a) -> a -> a -> a -> a -> Bool
propMonoid o u x y z = propAssociative o x y z && propUnit o u x

propDioid :: Eq a =>
             (a -> a -> a) -> a -> (a -> a -> a) -> a -> a -> a -> a -> Bool
propDioid p n o u x y z = propBoundedSemiLattice p n x y z
                       && propMonoid o u x y z
                       && propDistributive o p x y z
                       && propZero o n x

-- | Properties of 'Dioid' class.
propDioid_Gen :: Dioid a => a -> a -> a -> Bool
propDioid_Gen = propDioid meet top compose unitCompose

-- | @Weight@ instance.
prop_Dioid_Weight :: Weight -> Weight -> Weight -> Bool
prop_Dioid_Weight x y z = propDioid_Gen x y z

-- | @Label@ instance.
prop_SemiLattice_Label :: Label -> Label -> Label -> Bool
prop_SemiLattice_Label x y z = propSemiLattice meet x y z

prop_Unit_Label :: Label -> Bool
prop_Unit_Label x = propUnit meet top x

prop_BoundedSemiLattice_Label :: Label -> Label -> Label -> Bool
prop_BoundedSemiLattice_Label x y z = propBoundedSemiLattice meet top x y z

prop_Monoid_Label :: Label -> Label -> Label -> Bool
prop_Monoid_Label x y z = propMonoid compose unitCompose x y z

prop_DistL_Label :: Label -> Label -> Label -> Bool
prop_DistL_Label x y z = propDistL compose meet x y z

prop_DistR_Label :: Label -> Label -> Label -> Bool
prop_DistR_Label x y z = propDistR compose meet x y z

prop_Dist_Label :: Label -> Label -> Label -> Bool
prop_Dist_Label x y z = propDistributive compose meet x y z

prop_Zero_Label :: Label -> Bool
prop_Zero_Label x = propZero compose top x

prop_Dioid_Label :: Label -> Label -> Label -> Bool
prop_Dioid_Label x y z = propDioid_Gen x y z

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
tests = testProperties "Internal.TypeChecking.SizedTypes" $allProperties
