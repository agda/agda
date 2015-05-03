-- RETIRED, Graph libraries now under Agda.Utils.Graph.AdjacencyMap

{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}

-- | Directed graphs (can of course simulate undirected graphs).
--
--   Represented as adjacency maps in both directions.
--
--   Each source node maps to a adjacency map of outgoing edges,
--   which is a map from target nodes to edges.
--   Symmetrically, each target node maintains a map of incoming edges.
--
--   This allows to get incoming and outgoing edges in O(log n) time where
--   @n@ is the number of nodes in the graph.

module Agda.Utils.Graph
  ( Graph(..)
  , invariant
  , edges
  , edgesFrom
  , edgesTo
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

import Prelude hiding (lookup, transpose)

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

import qualified Agda.Utils.Graph.AdjacencyMap.Unidirectional as Uni
import Agda.Utils.QuickCheck
import Agda.Utils.SemiRing
import Agda.Utils.TestHelpers

-- | @Graph s t e@ is a directed graph with
--   source nodes in @s@
--   target nodes in @t@
--   and edges in @e@.
--
--   Admits at most one edge between any two nodes.
--   Several edges can be modeled by using a collection type for @e@.
--
--   Represented as "adjacency list", or rather, adjacency map.
--   This allows to get all outgoing and incoming edges for a node
--   in @O(log n)@ time where @n@ is the number of nodes of the graph.

data Graph s t e = Graph
  { outgoing :: Map s (Map t e) -- ^ Forward edges.
  , incoming :: Map t (Map s e) -- ^ Backward eges.
  }
  deriving (Eq, Functor, Show)

data Edge s t e = Edge
  { source :: s  -- ^ Outgoing node.
  , target :: t  -- ^ Incoming node.
  , label  :: e  -- ^ Edge label (weight).
  } deriving (Eq, Functor, Show)

-- * Edge queries

-- | Turn a graph into a list of edges.  @O(n + e)@

edges :: (Ord s, Ord t) => Graph s t e -> [Edge s t e]
edges = outEdges

-- | The list of edges computed from @outgoing@.

outEdges :: (Ord s, Ord t) => Graph s t e -> [Edge s t e]
outEdges = outEdges' . outgoing

outEdges' :: (Ord s, Ord t) => Map s (Map t e) -> [Edge s t e]
outEdges' g =
  [ Edge s t e
  | (s, tes) <- Map.assocs g
  , (t, e)   <- Map.assocs tes
  ]

-- | The list of edges computed from @incoming@.

inEdges :: (Ord s, Ord t) => Graph s t e -> [Edge s t e]
inEdges = inEdges' . incoming

inEdges' :: (Ord s, Ord t) => Graph s t e -> [Edge s t e]
inEdges' g =
  [ Edge s t e
  | (t, ses) <- Map.assocs (incoming g)
  , (s, e)   <- Map.assocs ses
  ]

-- | 'outgoing' and 'incoming' can be computed from each other by 'remap'.

-- remap :: (Ord s, Ord t) => Map s (Map t e) -> Map t (Map s e)
-- remap

-- | Invariant for the graphs: @outEdges == inEdges@.

invariant :: (Ord s, Ord t) => Graph s t e -> [Edge s t e]
invariant g = Set.fromList (outEdges g) == Set.fromList (inEdges g)

-- | All edges originating in the given nodes.
--   (I.e., all outgoing edges for the given nodes.)
--
--   Roughly linear in the length of the result list @O(result)@.

edgesFrom :: (Ord s, Ord t) => Graph s t e -> [s] -> [Edge s t e]
edgesFrom (Graph g _) ss =
  [ Edge s t e
  | s <- ss
  , m <- maybeToList $ Map.lookup s g
  , (t, e) <- Map.assocs m
  ]

-- | All edges ending in the given nodes.
--   (I.e., all incoming edges for the given nodes.)
--
--   Roughly linear in the length of the result list @O(result)@.

edgesTo :: (Ord s, Ord t) => Graph s t e -> [t] -> [Edge s t e]
edgesTo (Graph _ g) ts =
  [ Edge s t e
  | t <- ts
  , m <- maybeToList $ Map.lookup t g
  , (s, e) <- Map.assocs m
  ]

-- | Lookup label of an edge.

lookup :: (Ord s, Ord t) => s -> t -> Graph s t e -> Maybe e
lookup s t (Graph o _) = Map.lookup t =<< Map.lookup s o

-- | Get a list of outgoing edges with target.

neighbours :: (Ord s, Ord t) => s -> Graph s t e -> [(t, e)]
neighbours s (Graph o _) = maybe [] Map.assocs $ Map.lookup s o

prop_neighbours s g =
  neighbours s g == map (\ Edge s t e -> (t,e)) (edgesFrom g [s])

-- * Node queries

-- | Returns all the nodes with outgoing edges.  @O(n)@.

sourceNodes :: (Ord s, Ord t) => Graph s t e -> Set s
sourceNodes = Map.keysSet . outgoing

-- | Returns all the nodes with incoming edges.  @O(n)@.

targetNodes :: (Ord s, Ord t) => Graph s t e -> Set t
targetNodes = Map.keysSet . incoming

-- | For homogeneous graphs, @(s = t)@ we can compute a set
--   of all nodes.
--
--   Structure @Nodes@ is for computing all nodes but also
--   remembering which were incoming and which outgoing.
--   This is mostly for efficiency reasons, to avoid recomputation
--   when all three sets are needed.

data Nodes n = Nodes
  { srcNodes :: Set n
  , tgtNodes :: Set n
  , allNodes :: Set n
  }

computeNodes :: (Ord n) => Graph n n e -> Nodes n
computeNodes g = Nodes srcs tgts (srcs `Set.union` tgts)
  where srcs = sourceNodes g
        tgts = targetNodes g

-- | The set of all nodes (outgoing and incoming).

nodes :: (Ord n) => Graph n n e -> Set n
nodes = allNodes . computeNodes

-- * Graph construction.

-- | Constructs a completely disconnected graph containing the given
--   nodes. @O(n)@.

fromNodes :: Ord n => [n] -> Graph n n e
fromNodes ns = Graph nset nset
  where nset = Map.fromList $ map (, Map.empty) ns

prop_nodes_fromNodes ns = nodes (fromNodes ns) == Set.fromList ns

-- | Constructs a graph from a list of edges.  O(e log n)

fromList :: (SemiRing e, Ord s, Ord t) => [Edge s t e] -> Graph s t e
fromList = fromListWith oplus

fromListWith :: (Ord s, Ord t) => (e -> e -> e) -> [Edge s t e] -> Graph s t e
fromListWith f = List.foldl' (flip (insertEdgeWith f)) empty

-- | Empty graph (no nodes, no edges).

empty :: Graph s t e
empty = Graph Map.empty Map.empty

-- | A graph with two nodes and a single connecting edge.

singleton :: (Ord s, Ord t) => s -> t -> e -> Graph s t e
singleton s t e = Graph o i
  where o = Map.insert s (Map.singleton t e)
        i = Map.insert t (Map.singleton s e)

-- | Insert an edge into the graph.

insert :: (SemiRing e, Ord s, Ord t) => s -> t -> e -> Graph s t e -> Graph s t e
insert = insertWith oplus

insertEdge :: (SemiRing e, Ord s, Ord t) => Edge s t e -> Graph s t e -> Graph s t e
insertEdge (Edge s t e) = insert s t e

-- | Insert an edge, possibly combining @old@ edge weight with @new@ weight by
--   given function @f@ into @f new old@.

insertWith :: (Ord s, Ord t) => (e -> e -> e) -> s -> t -> e -> Graph s t e -> Graph s t e
insertWith f s t e (Graph o i) = Graph (Map.alter (Just . ins) s o)
                                       (Map.alter (Just . int) t i)
  where ins Nothing  = Map.singleton t e
        ins (Just m) = Map.insertWith f t e m
        int Nothing  = Map.singleton s e
        int (Just m) = Map.insertWith f s e m

insertEdgeWith :: (Ord s, Ord t) => (e -> e -> e) -> Edge s t e -> Graph s t e -> Graph s t e
insertEdgeWith f (Edge s t e) = insertWith f s t e

-- | Left-biased union.

union :: (SemiRing e, Ord n) => Graph n e -> Graph n e -> Graph n e
union = unionWith oplus

unionWith :: (Ord s, Ord t) => (e -> e -> e) -> Graph s t e -> Graph s t e -> Graph s t e
unionWith f (Graph o1 i1) (Graph o2 i2) = Graph o i
  where o = Map.unionWith (Map.unionWith f) o1 o2
        i = Map.unionWith (Map.unionWith f) i1 i2

unions :: (SemiRing e, Ord n) => [Graph n e] -> Graph n e
unions = unionsWith oplus

unionsWith :: (Ord s, Ord t) => (e -> e -> e) -> [Graph s t e] -> Graph s t e
unionsWith f = List.foldl' (unionWith f) empty

prop_insert ::  (SemiRing e, Ord s, Ord t) => s -> t -> e -> Graph s t e -> Bool
prop_insert s t e g = insert s t e g == union g (singleton s t e)

-- * Graph reversal

-- | The opposite graph (with all edges reversed).

transpose :: Graph s t e -> Graph t s e
transpose (Graph o i) = Graph i o

-- * Graph deconstruction.

-- | Removes the given node, and all corresponding edges, from the graph.

removeNode :: Ord n => n -> Graph n e -> Graph n e
removeNode n (Graph g) =
  Graph $ Map.delete n $ Map.map (Map.delete n) g

-- | @removeEdge s t g@ removes the edge going from @s@ to @t@, if any.

removeEdge :: (Ord s, Ord t) => s -> t -> Graph s t e -> Graph s t e
removeEdge s t (Graph o i) = Graph o' i'
  where o' = Map.adjust (Map.delete t) s o
        i' = Map.adjust (Map.delete s) t i

filterEdges :: (Ord s, Ord t) => (e -> Bool) -> Graph s t e -> Graph s t e
filterEdges f (Graph o i) = Graph o' i'
  where
    o'     = Map.mapMaybe filt o
    filt m = if Map.null m' then Nothing else Just m' where m' = Map.filter f m
    i'     = remap o'

-- | The graph's strongly connected components, in reverse topological
-- order.

sccs' :: Ord n => Graph n e -> [Graph.SCC n]
sccs' g =
  Graph.stronglyConnComp .
  map (\n -> (n, n, map fst $ neighbours n g)) .
  Set.toList .
  nodes $
  g

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
transitiveClosure1 = loop
  where
  loop g | g == g'   = g
         | otherwise = loop g'
    where g' = growGraph g

  growGraph g = List.foldl' union g $ map newEdges $ edges g
    where
    newEdges (a, b, w) = case Map.lookup b (unGraph g) of
      Just es -> Graph $ Map.singleton a $ Map.map (otimes w) es
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
tests = runTests "Agda.Utils.Graph"

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
