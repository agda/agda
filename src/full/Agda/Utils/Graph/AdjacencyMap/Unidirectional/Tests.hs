{-# OPTIONS_GHC -fno-warn-missing-signatures #-}

{-# LANGUAGE CPP                        #-}
{-# LANGUAGE DoAndIfThenElse            #-}
{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE NoMonomorphismRestriction  #-}
{-# LANGUAGE TemplateHaskell            #-}

-- | Properties for graph library.

module Agda.Utils.Graph.AdjacencyMap.Unidirectional.Tests (tests) where

import Prelude hiding (null)


import Control.Monad

import Data.Function
import qualified Data.Graph as Graph
import qualified Data.List as List
import Data.Maybe
import qualified Data.Map as Map
import qualified Data.Set as Set

import Test.QuickCheck as QuickCheck

import Agda.TypeChecking.Positivity.Occurrence hiding (tests)

import Agda.Utils.Function (iterateUntil)
import Agda.Utils.Functor
import Agda.Utils.Graph.AdjacencyMap.Unidirectional as Graph
import Agda.Utils.List (distinct)
import Agda.Utils.Null as Null
import Agda.Utils.SemiRing
import Agda.Utils.Singleton (Singleton)
import qualified Agda.Utils.Singleton as Singleton
import Agda.Utils.TestHelpers

#include "undefined.h"
import Agda.Utils.Impossible

------------------------------------------------------------------------
-- * Generating random graphs
------------------------------------------------------------------------

-- | Generates a node from the graph. (Unless the graph is empty.)

nodeIn :: (Ord n, Arbitrary n) => Graph n n e -> Gen n
nodeIn g = elementsUnlessEmpty (Set.toList $ nodes g)

-- | Generates an edge from the graph. (Unless the graph contains no
-- edges.)

edgeIn :: (Arbitrary n, Arbitrary e) =>
          Graph n n e -> Gen (Edge n n e)
edgeIn g = elementsUnlessEmpty (edges g)

-- | Sample graph type used to test some graph algorithms.

type G = Graph N N E

-- | Sample edge type used to test some graph algorithms.

type E = Occurrence

-- | Sample node type used to test some graph algorithms.

newtype N = N (Positive Int)
  deriving (Arbitrary, Eq, Ord)

n :: Int -> N
n = N . Positive

instance Show N where
  show (N (Positive n)) = "n " ++ show n

-- | 'gaussJordanFloydWarshallMcNaughtonYamada' can be used to check
-- if any two nodes in a graph are connected.

data Connected = Disconnected | Connected
  deriving (Eq, Show)

instance SemiRing Connected where
  ozero = Disconnected
  oone  = Connected

  Disconnected `oplus` c = c
  Connected    `oplus` _ = Connected

  Disconnected `otimes` _ = Disconnected
  Connected    `otimes` c = c

instance StarSemiRing Connected where
  ostar _ = Connected

connectivityGraph :: Ord n => Graph n n e -> Graph n n Connected
connectivityGraph =
  gaussJordanFloydWarshallMcNaughtonYamada .
  fmap (const oone)

connected :: Ord n => Graph n n Connected -> n -> n -> Bool
connected g i j = Graph.lookup i j g == Just Connected

------------------------------------------------------------------------
-- * Graph properties
------------------------------------------------------------------------

-- prop_neighbours :: (Ord s, Ord t, Eq e) => s -> Graph s t e -> Bool
prop_neighbours :: N -> G -> Bool
prop_neighbours s g =
  neighbours s g == map (\ (Edge s t e) -> (t, e)) (edgesFrom g [s])

-- prop_nodes_fromNodes :: Ord n => [n] -> Bool
prop_nodes_fromNodes :: [N] -> Bool
prop_nodes_fromNodes ns = sourceNodes (fromNodes ns) == Set.fromList ns

prop_clean_discrete :: G -> Bool
prop_clean_discrete g =
  discrete g == (null . graph . clean) g

-- prop_insertWith :: (Eq e, Ord s, Ord t) =>
--                    (e -> e -> e) -> s -> t -> e -> Graph s t e -> Bool
prop_insertWith :: (E -> E -> E) -> N -> N -> E -> G -> Bool
prop_insertWith f s t e g =
  insertWith f s t e g == unionWith (flip f) g (singleton s t e)

-- -- This property only holds only if the edge is new.
-- prop_insert ::  (Ord s, Ord t) => s -> t -> e -> Graph s t e -> Bool
-- prop_insert s t e g = insert s t e g == union g (singleton s t e)

prop_sccs' :: G -> Bool
prop_sccs' g =
  nodes g == Set.fromList (concat components)
    &&
  all distinct components
    &&
  all (not . null) components
    &&
  disjoint (map Set.fromList components)
    &&
  all stronglyConnected components'
    &&
  noMissingStronglyConnectedNodes components
    &&
  reverseTopologicalOrder
  where
  components' = sccs' g
  components  = map Graph.flattenSCC components'

  disjoint []       = True
  disjoint (s : ss) = all (Set.null . Set.intersection s) ss
                        &&
                      disjoint ss

  connected' = connected (connectivityGraph g)

  stronglyConnected (Graph.AcyclicSCC n) = not (connected' n n)
  stronglyConnected (Graph.CyclicSCC ns) = and
    [ connected' i j
    | i <- ns
    , j <- ns
    ]

  noMissingStronglyConnectedNodes []         = True
  noMissingStronglyConnectedNodes (ns : nss) =
    and [ not (connected' j i && connected' i j)
        | i <- ns
        , j <- concat nss
        ]
      &&
    noMissingStronglyConnectedNodes nss

  reverseTopologicalOrder = and
    [ component i <= component j
    | Edge i j _ <- edges g
    ]
    where
    component k =
      head [ i
           | (i, ns) <- zip [1..] (reverse components)
           , k `elem` ns
           ]

prop_sccDAG :: G -> Bool
prop_sccDAG g =
  dagInvariant dag
    &&
  nodes g == Map.keysSet (dagNodeMap dag)
  where
  dag = sccDAG g

prop_oppositeDAG :: G -> Bool
prop_oppositeDAG g =
  dagInvariant (oppositeDAG (sccDAG g))

-- | Computes the transitive closure of the graph.
--
-- Note that this algorithm is not guaranteed to be correct (or
-- terminate) for arbitrary semirings.
--
-- This function operates on the entire graph at once.

transitiveClosure1 :: (Eq e, SemiRing e, Ord n) =>
                      Graph n n e -> Graph n n e
transitiveClosure1 = completeUntilWith (==) otimes oplus

-- | Computes the transitive closure of the graph.
--
-- Note that this algorithm is not guaranteed to be correct (or
-- terminate) for arbitrary semirings.
--
-- This function operates on the entire graph at once.

completeUntilWith :: (Ord n) => (Graph n n e -> Graph n n e -> Bool) ->
  (e -> e -> e) -> (e -> e -> e) -> Graph n n e -> Graph n n e
completeUntilWith done otimes oplus = iterateUntil done growGraph  where

  -- @growGraph g@ unions @g@ with @(s --> t) `compose` g@ for each
  -- edge @s --> t@ in @g@
  growGraph g = List.foldl' (unionWith oplus) g $ for (edges g) $ \ (Edge s t e) ->
    case Map.lookup t (graph g) of
      Just es -> Graph $ Map.singleton s $ Map.map (otimes e) es
      Nothing -> Graph.empty

-- | Equality modulo empty edges.
(~~) :: (Eq e, Ord s, Ord t, Null e) => Graph s t e -> Graph s t e -> Bool
(~~) = (==) `on` clean

prop_gaussJordanFloydWarshallMcNaughtonYamadaReference :: G -> Bool
prop_gaussJordanFloydWarshallMcNaughtonYamadaReference g =
  gaussJordanFloydWarshallMcNaughtonYamadaReference g ~~
  transitiveClosure1 g

prop_gaussJordanFloydWarshallMcNaughtonYamada :: G -> Property
prop_gaussJordanFloydWarshallMcNaughtonYamada g =
  QuickCheck.label sccInfo $
    gaussJordanFloydWarshallMcNaughtonYamada g ~~ transitiveClosure1 g
  where
  sccInfo =
    (if noSCCs <= 3 then "   " ++ show noSCCs
                    else ">= 4") ++
    " strongly connected component(s)"
    where noSCCs = length (sccs g)

prop_complete :: G -> Bool
prop_complete g =
  complete g ~~ transitiveClosure1 g

-- Andreas, 2015-07-21 Issue 1612:
-- May take forever due to exponential time of allTrails.
--
-- prop_allTrails_existence :: Property
-- prop_allTrails_existence =
--   forAll (scale (`div` 2) arbitrary :: Gen G) $ \g ->
--   forAll (nodeIn g) $ \i ->
--   forAll (nodeIn g) $ \j ->
--     null (allTrails i j g)
--       ==
--     not (connected (connectivityGraph g) i j)

-- | The 'Integer's should be non-negative.

data ExtendedNatural = Finite Integer | Infinite
  deriving (Eq, Ord, Show)

instance SemiRing ExtendedNatural where
  ozero = Finite 0
  oone  = Finite 1

  oplus (Finite m) (Finite n) = Finite (m + n)
  oplus Infinite   _          = Infinite
  oplus _          Infinite   = Infinite

  otimes (Finite m) (Finite n) = Finite (m * n)
  otimes (Finite 0) _          = Finite 0
  otimes _          (Finite 0) = Finite 0
  otimes Infinite   _          = Infinite
  otimes _          Infinite   = Infinite

instance StarSemiRing ExtendedNatural where
  ostar (Finite 0) = Finite 1
  ostar _          = Infinite


-- Andreas, 2015-07-21 Issue 1612:
-- May take forever due to exponential time of allTrails.
--
-- prop_allTrails_number :: Property
-- prop_allTrails_number =
--   forAll (scale (`div` 2) arbitrary :: Gen G) $ \g ->
--   forAll (nodeIn g) $ \i ->
--   forAll (nodeIn g) $ \j ->
--     Finite (List.genericLength (allTrails i j g))
--       <=
--     case Graph.lookup i j
--            (gaussJordanFloydWarshallMcNaughtonYamada
--               (fmap (const oone) g)) of
--       Just n  -> n
--       Nothing -> Finite 0

-- Node 10 is unreachable, so @allTrails _ 10 g1612@ takes forever
g1612 :: Graph N N E
g1612 = Graph $ Map.fromList
  [ (n  1,Map.fromList [(n 1,Unused   ),(n  9,StrictPos),(n 12,JustPos),(n 15,JustPos)])
  , (n  3,Map.fromList [(n 3,Unused   ),(n  8,StrictPos)])
  , (n  8,Map.fromList [(n 1,GuardPos ),(n  3,Mixed    ),(n 8,Unused),(n 9,JustPos),(n 11,StrictPos),(n 12,GuardPos),(n 15,JustPos)])
  , (n  9,Map.fromList [(n 1,JustNeg  ),(n  8,Mixed    ),(n 9,JustNeg),(n 11,StrictPos),(n 12,StrictPos)])
  , (n 10,Map.fromList [(n 1,JustPos  ),(n  8,StrictPos)])
  , (n 11,Map.fromList [(n 1,StrictPos),(n  8,JustNeg  ),(n 9,JustNeg),(n 11,JustNeg)])
  , (n 12,Map.fromList [(n 1,JustPos  ),(n 15,StrictPos)])
  , (n 15,Map.fromList [(n 1,JustPos  ),(n  8,GuardPos ),(n 11,Mixed),(n 12,Mixed)])
  ]

-- t1612t = allTrails (n 9) (n 10) g1612 -- FOREVER

g1612a = Graph $ Map.fromList
  [(n  1,Map.fromList [(n 2,JustNeg),(n 11,Mixed)])
  ,(n  2,Map.fromList [(n 1,JustNeg),(n 2,GuardPos),(n 4,GuardPos),(n 8,Unused),(n 11,Unused)])
  ,(n  4,Map.fromList [(n 2,GuardPos),(n 8,JustPos),(n 12,GuardPos)])
  ,(n  6,Map.fromList [(n 1,StrictPos),(n 11,Unused),(n 12,JustNeg)])
  ,(n  8,Map.fromList [(n 1,GuardPos),(n 4,JustPos),(n 8,JustPos)])
  ,(n 11,Map.fromList [(n 4,GuardPos),(n 12,StrictPos)])
  ,(n 12,Map.fromList [(n 1,Mixed),(n 4,Mixed),(n 11,Mixed)])
  ]


------------------------------------------------------------------------
-- * All tests
------------------------------------------------------------------------

-- Template Haskell hack to make the following $quickCheckAll work
-- under ghc-7.8.
return [] -- KEEP!

-- | All tests as collected by 'quickCheckAll'.
--
--   Using 'quickCheckAll' is convenient and superior to the manual
--   enumeration of tests, since the name of the property is
--   added automatically.

tests :: IO Bool
tests = do
  putStrLn "Agda.Utils.Graph.AdjacencyMap.Unidirectional"
  $quickCheckAll


-- Abbreviations for testing in interpreter

g1, g2, g3, g4 :: Graph N N E
g1 = Graph $ Map.fromList
  [ (n 1, Map.fromList [(n 2,Unused)])
  , (n 2, Map.fromList [(n 1,Unused)])
  ]

g2 = Graph $ Map.fromList
  [ (n 1, Map.fromList [(n 2,StrictPos)])
  , (n 2, Map.fromList [(n 1,StrictPos)])
  ]

g3 = Graph $ Map.fromList
  [ (n 1, Map.fromList [(n 2,StrictPos)])
  , (n 2, Map.fromList [])
  , (n 4, Map.fromList [(n 1,StrictPos)])
  ]

g4 = Graph $ Map.fromList
  [ (n 1, Map.fromList [(n 6,Unused)])
  , (n 6, Map.fromList [(n 8,StrictPos)])
  , (n 8, Map.fromList [(n 3,Unused)])
  ]
