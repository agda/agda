{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE TupleSections #-}

-- | Directed graphs (can of course simulate undirected graphs).
--
--   Represented as adjacency maps.
--
--   Each source node maps to a adjacency map, which is a map from
--   target nodes to edges.
--
--   This allows to get the outgoing edges in O(log n) time where
--   @n@ is the number of nodes in the graph.  However, the set
--   of incoming edges can only be obtained in O(n log n),
--   or O(e) where @e@ is the total number of edges.

-- used for positivity checker

module Agda.Utils.Graph.AdjacencyMap
  ( Graph(..)
  , invariant
  , edges
  , edgesFrom
  , nodes
  , filterEdges
  , fromNodes
  , fromList
  , empty
  , singleton
  , insert
  , removeNode
  , removeEdge
  , union
  , unions
  , lookup
  , neighbours
  , sccs'
  , sccs
  , acyclic
  , transitiveClosure1
  , transitiveClosure
  , findPath
  , allPaths
  , nodeIn
  , edgeIn
  , tests
  )
  where

import Prelude hiding (lookup)

import Control.Applicative ((<$>), (<*>))

import Data.Function
import qualified Data.Graph as Graph
import qualified Data.List as List
import qualified Data.Map as Map
import Data.Map (Map)
import qualified Data.Maybe as Maybe
import Data.Maybe (maybeToList)
import qualified Data.Set as Set
import Data.Set (Set)

import Agda.Utils.Function (iterateUntil)
import Agda.Utils.Functor (for)
import Agda.Utils.QuickCheck
import Agda.Utils.SemiRing
import Agda.Utils.TestHelpers

-- | @Graph n e@ is a directed graph with nodes in @n@ and edges in @e@.
--
--   Only one edge between any two nodes.
--
--   Represented as "adjacency list", or rather, adjacency map.
--   This allows to get all outgoing edges for a node in @O(log n)@ time
--   where @n@ is the number of nodes of the graph.
--   Incoming edges can only be computed in @O(n + e)@ time where
--   @e@ is the number of edges.
newtype Graph n e = Graph { unGraph :: Map n (Map n e) }
  deriving (Eq, Functor, Show)

-- | A structural invariant for the graphs.
--
--   The set of nodes is obtained by @Map.keys . unGraph@
--   meaning that each node, be it only the target of an edge,
--   must be assigned an adjacency map, albeit it could be empty.
--
--   See 'singleton'.
invariant :: Ord n => Graph n e -> Bool
invariant g = connectedNodes `Set.isSubsetOf` nodes g
  where
  connectedNodes =
    Set.fromList $ concatMap (\(a, b, _) -> [a, b]) $ edges g

-- | Turn a graph into a list of edges.  @O(n + e)@

edges :: Ord n => Graph n e -> [(n, n, e)]
edges g = [ (from, to, w) | (from, es) <- Map.assocs (unGraph g)
                          , (to, w)    <- Map.assocs es ]

-- | All edges originating in the given nodes.
--   (I.e., all outgoing edges for the given nodes.)
--
--   Roughly linear in the length of the result list @O(result)@.

edgesFrom :: Ord n => Graph n e -> [n] -> [(n, n, e)]
edgesFrom (Graph g) ns =
  [ (n1, n2, w) | n1 <- ns
                , m <- maybeToList $ Map.lookup n1 g
                , (n2, w) <- Map.assocs m
                ]

-- | Returns all the nodes in the graph.  @O(n)@.

nodes :: Ord n => Graph n e -> Set n
nodes g = Map.keysSet (unGraph g)

-- | Constructs a completely disconnected graph containing the given
--   nodes. @O(n)@.

fromNodes :: Ord n => [n] -> Graph n e
fromNodes = Graph . Map.fromList . map (, Map.empty)

prop_nodes_fromNodes :: Ord n => [n] -> Bool
prop_nodes_fromNodes ns = nodes (fromNodes ns) == Set.fromList ns

-- | Constructs a graph from a list of edges.  O(e)

fromList :: (SemiRing e, Ord n) => [(n, n, e)] -> Graph n e
fromList es = unions [ singleton a b w | (a, b, w) <- es ]

-- | Empty graph (no nodes, no edges).

empty :: Graph n e
empty = Graph Map.empty

-- | A graph with two nodes and a single connecting edge.

singleton :: Ord n => n -> n -> e -> Graph n e
singleton a b w =
  Graph $ Map.insert a (Map.singleton b w) $ Map.singleton b Map.empty

-- | Insert an edge into the graph.

-- Andreas, 2014-02-12 For my taste, this relies a bit
-- too much on the efficieny of union.
-- In Data.Map (hedge union) it is described as linear in g, which is
-- probably too pessimistic.
-- I prefer an implementation of insert in terms of Map.insertWith.

insert :: (SemiRing e, Ord n) => n -> n -> e -> Graph n e -> Graph n e
insert from to w g = union g (singleton from to w)

-- | Removes the given node, and all corresponding edges, from the
-- graph.

removeNode :: Ord n => n -> Graph n e -> Graph n e
removeNode n (Graph g) =
  Graph $ Map.delete n $ Map.map (Map.delete n) g

-- | @removeEdge n1 n2 g@ removes the edge going from @n1@ to @n2@, if
-- any.

removeEdge :: Ord n => n -> n -> Graph n e -> Graph n e
removeEdge n1 n2 (Graph g) =
  Graph $ Map.adjust (Map.delete n2) n1 g

filterEdges :: Ord n => (e -> Bool) -> Graph n e -> Graph n e
filterEdges f (Graph g) = Graph $ Map.mapMaybe filt g
  where filt m =
         let m' = Map.filter f m
         in  if Map.null m' then Nothing else Just m'

union :: (SemiRing e, Ord n) => Graph n e -> Graph n e -> Graph n e
union (Graph g1) (Graph g2) =
  Graph $ Map.unionWith (Map.unionWith oplus) g1 g2

unions :: (SemiRing e, Ord n) => [Graph n e] -> Graph n e
unions = List.foldl' union empty

lookup :: Ord n => n -> n -> Graph n e -> Maybe e
lookup a b g = Map.lookup b =<< Map.lookup a (unGraph g)

neighbours :: Ord n => n -> Graph n e -> [(n, e)]
neighbours a g = maybe [] Map.assocs $ Map.lookup a $ unGraph g

-- | The graph's strongly connected components, in reverse topological
-- order.

sccs' :: Ord n => Graph n e -> [Graph.SCC n]
sccs' (Graph g) =
  Graph.stronglyConnComp [ (n, n, Map.keys m) | (n, m) <- Map.assocs g ]

-- | The graph's strongly connected components, in reverse topological
-- order.

sccs :: Ord n => Graph n e -> [[n]]
sccs = map Graph.flattenSCC . sccs'

-- | Returns @True@ iff the graph is acyclic.

acyclic :: Ord n => Graph n e -> Bool
acyclic = all isAcyclic . sccs'
  where
  isAcyclic Graph.AcyclicSCC{} = True
  isAcyclic Graph.CyclicSCC{}  = False

-- | Computes the transitive closure of the graph.
--
-- Note that this algorithm is not guaranteed to be correct (or
-- terminate) for arbitrary semirings.
--
-- This function operates on the entire graph at once.

transitiveClosure1 :: (Eq e, SemiRing e, Ord n) =>
                      Graph n e -> Graph n e
transitiveClosure1 = iterateUntil (==) growGraph  where

  -- @growGraph g@ unions @g@ with @(s --> t) `compose` g@ for each
  -- edge @s --> t@ in @g@
  growGraph g = List.foldl' union g $ for (edges g) $ \ (s, t, e) ->
    case Map.lookup t (unGraph g) of
      Just es -> Graph $ Map.singleton s $ Map.map (otimes e) es
      Nothing -> empty

-- | Computes the transitive closure of the graph.
--
-- Note that this algorithm is not guaranteed to be correct (or
-- terminate) for arbitrary semirings.
--
-- This function operates on one strongly connected component at a
-- time.

transitiveClosure :: (Eq e, SemiRing e, Ord n) => Graph n e -> Graph n e
transitiveClosure g = List.foldl' extend g $ sccs' g
  where
  edgesFrom' g ns = (g, edgesFrom g ns)

  extend g (Graph.AcyclicSCC scc) = fst $ growGraph [scc] (edgesFrom' g [scc])
  extend g (Graph.CyclicSCC  scc) = loop (edgesFrom' g scc)
    where
    loop g | equal g g' = fst g
           | otherwise  = loop g'
      where g' = growGraph scc g

    equal = (==) `on` snd

  growGraph scc (g, es) =
    edgesFrom' (List.foldl' union g $ map newEdges es) scc
    where
    newEdges (a, b, w) = case Map.lookup b (unGraph g) of
      Just es -> Graph $ Map.singleton a $ Map.map (otimes w) es
      Nothing -> empty

prop_transitiveClosure :: (Eq e, SemiRing e, Ord n) => Graph n e -> Property
prop_transitiveClosure g = label sccInfo $
  transitiveClosure g == transitiveClosure1 g
  where
  sccInfo =
    (if noSCCs <= 3 then "   " ++ show noSCCs
                    else ">= 4") ++
    " strongly connected component(s)"
    where noSCCs = length (sccs g)

findPath :: (SemiRing e, Ord n) => (e -> Bool) -> n -> n -> Graph n e -> Maybe e
findPath good a b g = case filter good $ allPaths good a b g of
  []    -> Nothing
  w : _ -> Just w

-- | @allPaths classify a b g@ returns a list of pathes (accumulated edge weights)
--   from node @a@ to node @b@ in @g@.
--   Alternative intermediate pathes are only considered if they
--   are distinguished by the @classify@ function.
allPaths :: (SemiRing e, Ord n, Ord c) => (e -> c) -> n -> n -> Graph n e -> [e]
allPaths classify a b g = paths Set.empty a
  where
    paths visited a = concatMap step $ neighbours a g
      where
        step (c, w)
          | Set.member tag visited = []
          | otherwise = found ++
                        map (otimes w)
                          (paths (Set.insert tag visited) c)
          where tag = (c, classify w)
                found | b == c    = [w]
                      | otherwise = []

------------------------------------------------------------------------
-- Utilities used to test the code above

instance (Ord n, SemiRing e, Arbitrary n, Arbitrary e) =>
         Arbitrary (Graph n e) where
  arbitrary = do
    nodes <- sized $ \n -> resize (isqrt n) arbitrary
    edges <- mapM (\(n1, n2) -> (n1, n2,) <$> arbitrary) =<<
                  listOfElements ((,) <$> nodes <*> nodes)
    return (fromList edges `union` fromNodes nodes)
    where
    isqrt :: Int -> Int
    isqrt = round . sqrt . fromIntegral

  shrink g =
    [ removeNode n g     | n <- Set.toList $ nodes g ] ++
    [ removeEdge n1 n2 g | (n1, n2, _) <- edges g ]

-- | Generates a node from the graph. (Unless the graph is empty.)

nodeIn :: (Ord n, Arbitrary n) => Graph n e -> Gen n
nodeIn g = elementsUnlessEmpty (Set.toList $ nodes g)

-- | Generates an edge from the graph. (Unless the graph contains no
-- edges.)

edgeIn :: (Ord n, Arbitrary n, Arbitrary e) =>
          Graph n e -> Gen (n, n, e)
edgeIn g = elementsUnlessEmpty (edges g)

-- | Used to test 'transitiveClosure' and 'transitiveClosure1'.

type G = Graph Int E

-- | Used to test 'transitiveClosure' and 'transitiveClosure1'.

newtype E = E { unE :: Bool }
  deriving (Arbitrary, Eq, Show)

instance SemiRing E where
  oplus  (E x) (E y) = E (x || y)
  otimes (E x) (E y) = E (x && y)

-- | All tests.

tests :: IO Bool
tests = runTests "Agda.Utils.Graph.AdjacencyMap"

    -- Make sure that the invariant is established/preserved.
  [ quickCheck' invariant'
  , quickCheck' (all invariant' . shrink)
  , quickCheck' (invariant' . fromNodes)
  , quickCheck' (invariant' . fromList)
  , quickCheck' (invariant' empty)
  , quickCheck' (\n1 n2 w -> invariant' (singleton n1 n2 w))
  , quickCheck' (\n1 n2 w g -> invariant' (insert n1 n2 w g))
  , quickCheck' (\g n -> invariant' (removeNode n g))
  , quickCheck' (\g -> forAll (nodeIn g) $ \n ->
                    invariant' (removeNode n g))
  , quickCheck' (\g n1 n2 -> invariant' (removeEdge n1 n2 g))
  , quickCheck' (\g -> forAll (edgeIn g) $ \(n1, n2, _) ->
                    invariant' (removeEdge n1 n2 g))
  , quickCheck' (\g1 g2 -> invariant' (union g1 g2))
  , quickCheck' (invariant' . unions)
  , quickCheck' (invariant' . transitiveClosure1)
  , quickCheck' (invariant' . transitiveClosure)

    -- Other properties.
  , quickCheck' (prop_nodes_fromNodes :: [Int] -> Bool)
  , quickCheck' (prop_transitiveClosure :: G -> Property)
  ]
  where
  invariant' :: G -> Bool
  invariant' = invariant
