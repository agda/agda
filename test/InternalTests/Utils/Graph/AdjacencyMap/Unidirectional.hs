{-# OPTIONS_GHC -fno-warn-missing-signatures #-}

{-# LANGUAGE CPP                        #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE NoMonomorphismRestriction  #-}
{-# LANGUAGE TemplateHaskell            #-}

-- | Properties for graph library.

module InternalTests.Utils.Graph.AdjacencyMap.Unidirectional ( tests ) where

import Agda.TypeChecking.Positivity.Occurrence

import Agda.Utils.Function (iterateUntil)
import Agda.Utils.Functor
import Agda.Utils.Graph.AdjacencyMap.Unidirectional as Graph
import Agda.Utils.List (distinct)
import Agda.Utils.Null as Null
import Agda.Utils.SemiRing
import Agda.Utils.Singleton (Singleton)
import qualified Agda.Utils.Singleton as Singleton
import Agda.Utils.Impossible

#if __GLASGOW_HASKELL__ <= 708
import Control.Applicative ( (<$>), (<*>) )
#endif

import Control.Monad

import qualified Data.Foldable as Fold
import Data.Function
import qualified Data.Graph as Graph
import qualified Data.List as List
import Data.Maybe
import qualified Data.Map as Map
import qualified Data.Set as Set

import InternalTests.Helpers
import InternalTests.TypeChecking.Positivity.Occurrence ()

import Prelude hiding (null)

import Test.QuickCheck as QuickCheck

#include "undefined.h"

------------------------------------------------------------------------
-- Generators

instance (Arbitrary s, Arbitrary t, Arbitrary e) => Arbitrary (Edge s t e) where
  arbitrary = Edge <$> arbitrary <*> arbitrary <*> arbitrary

instance (CoArbitrary s, CoArbitrary t, CoArbitrary e) => CoArbitrary (Edge s t e) where
  coarbitrary (Edge s t e) = coarbitrary s . coarbitrary t . coarbitrary e

instance (Ord n, Arbitrary n, Arbitrary e) =>
         Arbitrary (Graph n n e) where
  arbitrary = do
    nodes <- sized $ \ n -> resize (2 * isqrt n) arbitrary
    edges <- mapM (\ (n1, n2) -> Edge n1 n2 <$> arbitrary) =<<
                  listOfElements ((,) <$> nodes <*> nodes)
    let g1 = fromList edges
        g2 = g1 `union` fromNodes nodes
    elements [ g1  -- Does not contain empty outermost node maps.
             , g2  -- May contain empty outermost node maps.
             ]
    where
    isqrt :: Int -> Int
    isqrt = round . sqrt . fromIntegral

  shrink g =
    [ removeNode n g     | n <- Set.toList $ nodes g ] ++
    [ removeEdge n1 n2 g | Edge n1 n2 _ <- edges g ]

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
  fst . gaussJordanFloydWarshallMcNaughtonYamada .
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

-- | @isWalk g from to es@ is 'True' iff @es@ is a walk from @from@ to
-- @to@ in @g@.

isWalk :: G -> N -> N -> [Edge N N E] -> Bool
isWalk g from to [] =
  from == to
    &&
  from `Set.member` nodes g
isWalk g from to es =
  map source es ++ [to] == [from] ++ map target es
    &&
  all validEdge es
  where
  validEdge e = e `elem` edgesFrom g [source e]

prop_reachableFrom :: G -> Property
prop_reachableFrom g =
  not (Set.null (nodes g)) ==>
  forAll (nodeIn g) $ \ u ->
    let reachableFromU = reachableFrom g u in
    -- Every list is a walk of the given length.
    all (\(v, (n, es)) -> isWalk g u v es && length es == n)
        (Map.toList reachableFromU)
      &&
    -- Every walk is a simple path.
    Fold.all (distinct . map source . snd) reachableFromU
      &&
    -- A path is found from u to v iff u = v or there is a non-empty
    -- path from u to v (according to 'connectivityGraph' and
    -- 'connected').
    Fold.all (\v -> Map.member v reachableFromU
                      ==
                    (u == v || connected cg u v))
             (nodes g)
  where
  cg = connectivityGraph g

prop_walkSatisfying ::
  G -> (Occurrence -> Bool) -> (Occurrence -> Bool) -> Property
prop_walkSatisfying g every some =
  forAll (nodeIn g) $ \from ->
  forAll (nodeIn g) $ \to ->
    case walkSatisfying every some g from to of
      Nothing -> QuickCheck.label "no walk" True
      Just es -> QuickCheck.label (show (length es) ++ " steps") $
                   isWalk g from to es
                     &&
                   all every es' && any some es'
        where es' = map Graph.label es

-- | A property for
-- 'Agda.TypeChecking.Positivity.Occurrence.productOfEdgesInBoundedWalk'.

prop_productOfEdgesInBoundedWalk :: G -> Property
prop_productOfEdgesInBoundedWalk g =
  forAll (nodeIn g) $ \ u ->
  forAll (nodeIn g) $ \v ->
  forAll (elements (Map.keys boundToEverySome)) $ \bound ->
    case productOfEdgesInBoundedWalk id g u v bound of
      Nothing -> Nothing
      Just o  -> Just (o <= bound)
      ==
    case Graph.lookup u v
           (fst (gaussJordanFloydWarshallMcNaughtonYamada g)) of
      Just o | o <= bound -> Just True
      _                   -> Nothing

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
    fst (gaussJordanFloydWarshallMcNaughtonYamada g) ~~
    transitiveClosure1 g
  where
  sccInfo =
    (if noSCCs <= 3 then "   " ++ show noSCCs
                    else ">= 4") ++
    " strongly connected component(s)"
    where noSCCs = length (sccs g)

prop_complete :: G -> Bool
prop_complete g =
  complete g ~~ transitiveClosure1 g

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
  putStrLn "InternalTests.Utils.Graph.AdjacencyMap.Unidirectional"
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
