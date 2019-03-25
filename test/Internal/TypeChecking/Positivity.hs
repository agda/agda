{-# LANGUAGE TemplateHaskell #-}

module Internal.TypeChecking.Positivity ( tests ) where

import Data.Sequence (Seq)

import Agda.TypeChecking.Positivity
import Agda.TypeChecking.Positivity.Occurrence

import Agda.Utils.SemiRing

import Internal.Helpers
import Internal.TypeChecking.Positivity.Occurrence ()

------------------------------------------------------------------------
-- * Generators and tests
------------------------------------------------------------------------

instance Arbitrary a => Arbitrary (Edge a) where
  arbitrary = Edge <$> arbitrary <*> arbitrary

  shrink (Edge o w) = [ Edge o w | o <- shrink o ] ++
                      [ Edge o w | w <- shrink w ]

instance CoArbitrary a => CoArbitrary (Edge a) where
  coarbitrary (Edge o w) = coarbitrary (o, w)

------------------------------------------------------------------------------

-- | The 'oplus' method for 'Occurrence' matches that for @'Edge'
-- ('Seq' 'OccursWhere')@.

prop_oplus_Occurrence_Edge ::
  Edge (Seq OccursWhere) -> Edge (Seq OccursWhere) -> Bool
prop_oplus_Occurrence_Edge e1@(Edge o1 _) e2@(Edge o2 _) =
  case oplus e1 e2 of
    Edge o _ -> o == oplus o1 o2

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
tests = testProperties "Internal.TypeChecking.Positivity" $allProperties
