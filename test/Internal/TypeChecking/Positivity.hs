{-# LANGUAGE TemplateHaskell #-}

module Internal.TypeChecking.Positivity ( tests ) where

import Data.Sequence (Seq)

import Agda.TypeChecking.Positivity
import Agda.TypeChecking.Positivity.Occurrence (Occurrence(..))
import Agda.TypeChecking.Positivity.OccurrenceAnalysis (Node(..))
import Agda.TypeChecking.Positivity.Warnings

import Agda.Utils.SemiRing
import Agda.Utils.Graph.AdjacencyMap.Unidirectional qualified as Graph

import Internal.Helpers
import Internal.TypeChecking.Positivity.Occurrence ()
import Internal.Utils.Graph.AdjacencyMap.Unidirectional (nodeIn)

------------------------------------------------------------------------
-- * Generators and tests
------------------------------------------------------------------------

instance Arbitrary a => Arbitrary (Edge a) where
  arbitrary = Edge <$> arbitrary <*> arbitrary

  shrink (Edge o w) = [ Edge o w | o <- shrink o ] ++
                      [ Edge o w | w <- shrink w ]

instance CoArbitrary a => CoArbitrary (Edge a) where
  coarbitrary (Edge o w) = coarbitrary (o, w)

instance Arbitrary Node where
  arbitrary = oneof [DefNode <$> arbitrary, ArgNode <$> arbitrary <*> arbitrary]

------------------------------------------------------------------------------

-- | The 'oplus' method for 'Occurrence' matches that for @'Edge'
-- ('Seq' 'OccursWhere')@.

prop_oplus_Occurrence_Edge ::
  Edge (Seq OccursWhere) -> Edge (Seq OccursWhere) -> Bool
prop_oplus_Occurrence_Edge e1@(Edge o1 _) e2@(Edge o2 _) =
  case oplus e1 e2 of
    Edge o _ -> o == oplus o1 o2

-- -- | 'transitiveOccurrence' gives the same result as looking up from
-- --   the transitive closure of the graph.
-- prop_transitiveOccurrence :: Graph.Graph Node (Edge OccursWhere) -> Property
-- prop_transitiveOccurrence g =
--   let gstar = Graph.transitiveClosure (fmap (\(Edge o _) -> o) g) in
--   forAll (nodeIn g) \n ->
--   forAll (nodeIn g) \m ->
--     maybe Unused id (Graph.lookup n m gstar)
--     ==
--     transitiveOccurrence g n m

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
