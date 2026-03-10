{-# LANGUAGE TemplateHaskell #-}

module Internal.TypeChecking.Positivity ( tests ) where

import Data.Sequence (Seq)
import System.IO.Unsafe

import Agda.TypeChecking.Positivity
import Agda.TypeChecking.Positivity.Occurrence (Occurrence(..))
import Agda.TypeChecking.Positivity.OccurrenceAnalysis (Node(..), fromGenericGraph, transitiveOccurrence)
import Agda.TypeChecking.Positivity.Warnings qualified as W

import Agda.Utils.SemiRing
import Agda.Utils.Graph.AdjacencyMap.Unidirectional qualified as Graph

import Internal.Helpers
import Internal.TypeChecking.Positivity.Occurrence ()
import Internal.Utils.Graph.AdjacencyMap.Unidirectional (nodeIn)

------------------------------------------------------------------------
-- * Generators and tests
------------------------------------------------------------------------

instance Arbitrary a => Arbitrary (W.Edge a) where
  arbitrary = W.Edge <$> arbitrary <*> arbitrary

  shrink (W.Edge o w) = [ W.Edge o w | o <- shrink o ] ++
                      [ W.Edge o w | w <- shrink w ]

instance CoArbitrary a => CoArbitrary (W.Edge a) where
  coarbitrary (W.Edge o w) = coarbitrary (o, w)

instance Arbitrary Node where
  arbitrary = oneof [DefNode <$> arbitrary, ArgNode <$> arbitrary <*> arbitrary]

------------------------------------------------------------------------------

-- | The 'oplus' method for 'Occurrence' matches that for @'Edge'
-- ('Seq' 'OccursWhere')@.

prop_oplus_Occurrence_Edge ::
  W.Edge (Seq W.OccursWhere) -> W.Edge (Seq W.OccursWhere) -> Bool
prop_oplus_Occurrence_Edge e1@(W.Edge o1 _) e2@(W.Edge o2 _) =
  case oplus e1 e2 of
    W.Edge o _ -> o == oplus o1 o2

-- | 'transitiveOccurrence' gives the same result as looking up from
--   the transitive closure of the graph.
prop_transitiveOccurrence :: Graph.Graph Node (W.Edge ()) -> Property
prop_transitiveOccurrence g =
  let gstar = Graph.transitiveClosure (fmap (\(W.Edge o _) -> o) g) in
  let g' = fromGenericGraph g in
  forAll (nodeIn g) \n ->
  forAll (nodeIn g) \m ->
    maybe Unused id (Graph.lookup n m gstar)
    ==
    unsafeDupablePerformIO (transitiveOccurrence g' n m)

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
