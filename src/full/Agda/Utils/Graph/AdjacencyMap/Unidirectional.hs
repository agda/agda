{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DoAndIfThenElse #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE TupleSections #-}

-- | Directed graphs (can of course simulate undirected graphs).
--
--   Represented as adjacency maps in direction from source to target.
--
--   Each source node maps to a adjacency map of outgoing edges,
--   which is a map from target nodes to edges.
--
--   This allows to get outgoing edges in O(log n) time where
--   @n@ is the number of nodes in the graph.

module Agda.Utils.Graph.AdjacencyMap.Unidirectional
  ( Graph(..)
  , Edge(..)
  , transposeEdge
  , edges
  , edgesFrom
  , edgesTo
  , diagonal
  , lookup
  , neighbours
  , sourceNodes, targetNodes
  , Nodes(..)
  , computeNodes, nodes
  , fromNodes
  , fromList, fromListWith
  , toList
  , empty
  , singleton
  , insert, insertWith
  , insertEdge, insertEdgeWith
  , union , unionWith
  , unions, unionsWith
  , removeNode
  , removeEdge
  , filterEdges
  , unzip
  , sccs'
  , sccs
  , acyclic
  , composeWith
  , transitiveClosure1
  , transitiveClosure
  , findPath
  , allPaths
  , nodeIn
  , edgeIn
  , tests
  )
  where

import Prelude hiding (lookup, unzip)

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
import Agda.Utils.List (headMaybe)
import Agda.Utils.QuickCheck as QuickCheck
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
--   This allows to get all outgoing edges for a node
--   in @O(log n)@ time where @n@ is the number of nodes of the graph.

newtype Graph s t e = Graph
  { graph :: Map s (Map t e) -- ^ Forward edges.
  }
  deriving (Eq, Functor, Show)

data Edge s t e = Edge
  { source :: s  -- ^ Outgoing node.
  , target :: t  -- ^ Incoming node.
  , label  :: e  -- ^ Edge label (weight).
  } deriving (Eq, Ord, Functor, Show)

-- | Reverse an edge.

transposeEdge :: Edge s t e -> Edge t s e
transposeEdge (Edge s t e) = Edge t s e

-- * Edge queries

-- | Turn a graph into a list of edges.  @O(n + e)@

edges :: (Ord s, Ord t) => Graph s t e -> [Edge s t e]
edges (Graph g) =
  [ Edge s t e
  | (s, tes) <- Map.assocs g
  , (t, e)   <- Map.assocs tes
  ]

-- | All edges originating in the given nodes.
--   (I.e., all outgoing edges for the given nodes.)
--
--   Roughly linear in the length of the result list @O(result)@.

edgesFrom :: (Ord s, Ord t) => Graph s t e -> [s] -> [Edge s t e]
edgesFrom (Graph g) ss =
  [ Edge s t e
  | s <- ss
  , m <- maybeToList $ Map.lookup s g
  , (t, e) <- Map.assocs m
  ]


-- | All edges ending in the given nodes.
--   (I.e., all incoming edges for the given nodes.)
--
--   Expensive: @O(n * |ts| * log n)@.

edgesTo :: (Ord s, Ord t) => Graph s t e -> [t] -> [Edge s t e]
edgesTo (Graph g) ts =
  [ Edge s t e
  | (s, m) <- Map.assocs g
  , t <- ts
  , e <- maybeToList $ Map.lookup t m
  ]

-- | Get all self-loops.

diagonal :: (Ord n) => Graph n n e -> [Edge n n e]
diagonal (Graph g) =
  [ Edge s s e
  | (s, m) <- Map.assocs g
  , e      <- maybeToList $ Map.lookup s m
  ]

-- | Lookup label of an edge.

lookup :: (Ord s, Ord t) => s -> t -> Graph s t e -> Maybe e
lookup s t (Graph g) = Map.lookup t =<< Map.lookup s g

-- | Get a list of outgoing edges with target.

neighbours :: (Ord s, Ord t) => s -> Graph s t e -> [(t, e)]
neighbours s (Graph g) = maybe [] Map.assocs $ Map.lookup s g

prop_neighbours :: (Ord s, Ord t, Eq e) => s -> Graph s t e -> Bool
prop_neighbours s g =
  neighbours s g == map (\ (Edge s t e) -> (t, e)) (edgesFrom g [s])

-- * Node queries

-- | Returns all the nodes with outgoing edges.  @O(n)@.

sourceNodes :: (Ord s, Ord t) => Graph s t e -> Set s
sourceNodes = Map.keysSet . graph

-- | Returns all the nodes with incoming edges.  Expensive! @O(e)@.

targetNodes :: (Ord s, Ord t) => Graph s t e -> Set t
targetNodes = Set.fromList . map target . edges

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
fromNodes ns = Graph $ Map.fromList $ map (, Map.empty) ns

prop_nodes_fromNodes :: Ord n => [n] -> Bool
prop_nodes_fromNodes ns = sourceNodes (fromNodes ns) == Set.fromList ns

-- | Constructs a graph from a list of edges.  O(e log n)
--
--   Later edges overwrite earlier edges.

fromList :: (Ord s, Ord t) => [Edge s t e] -> Graph s t e
fromList = fromListWith $ \ new old -> new

-- | Constructs a graph from a list of edges.  O(e log n)
--
--   Later edges are combined with earlier edges using the supplied function.

fromListWith :: (Ord s, Ord t) => (e -> e -> e) -> [Edge s t e] -> Graph s t e
fromListWith f = List.foldl' (flip (insertEdgeWith f)) empty

-- | Convert a graph into a list of edges. O(e)

toList :: (Ord s, Ord t) => Graph s t e -> [Edge s t e]
toList (Graph g) = [ Edge s t a | (s,m) <- Map.assocs g, (t,a) <- Map.assocs m ]

-- | Empty graph (no nodes, no edges).

empty :: Graph s t e
empty = Graph Map.empty

-- | A graph with two nodes and a single connecting edge.

singleton :: (Ord s, Ord t) => s -> t -> e -> Graph s t e
singleton s t e = Graph $ Map.singleton s (Map.singleton t e)

-- | Insert an edge into the graph.

insert :: (Ord s, Ord t) => s -> t -> e -> Graph s t e -> Graph s t e
insert = insertWith $ \ new old -> new

insertEdge :: (Ord s, Ord t) => Edge s t e -> Graph s t e -> Graph s t e
insertEdge (Edge s t e) = insert s t e

-- | Insert an edge, possibly combining @old@ edge weight with @new@ weight by
--   given function @f@ into @f new old@.

insertWith :: (Ord s, Ord t) =>
              (e -> e -> e) -> s -> t -> e -> Graph s t e -> Graph s t e
insertWith f s t e (Graph g) = Graph (Map.alter (Just . ins) s g)
  where ins Nothing  = Map.singleton t e
        ins (Just m) = Map.insertWith f t e m

insertEdgeWith :: (Ord s, Ord t) =>
                  (e -> e -> e) -> Edge s t e -> Graph s t e -> Graph s t e
insertEdgeWith f (Edge s t e) = insertWith f s t e

-- | Left-biased union.

union :: (Ord s, Ord t) => Graph s t e -> Graph s t e -> Graph s t e
union = unionWith $ \ left right -> left

unionWith :: (Ord s, Ord t) =>
             (e -> e -> e) -> Graph s t e -> Graph s t e -> Graph s t e
unionWith f (Graph g) (Graph g') = Graph $ Map.unionWith (Map.unionWith f) g g'

unions ::(Ord s, Ord t) => [Graph s t e] -> Graph s t e
unions = unionsWith $ \ left right -> left

unionsWith :: (Ord s, Ord t) => (e -> e -> e) -> [Graph s t e] -> Graph s t e
unionsWith f = List.foldl' (unionWith f) empty

prop_insertWith :: (Eq e, Ord s, Ord t) =>
                   (e -> e -> e) -> s -> t -> e -> Graph s t e -> Bool
prop_insertWith f s t e g =
  insertWith f s t e g == unionWith (flip f) g (singleton s t e)

{- This property only holds only if the edge is new.

prop_insert ::  (Ord s, Ord t) => s -> t -> e -> Graph s t e -> Bool
prop_insert s t e g = insert s t e g == union g (singleton s t e)
-}

-- * Graph reversal

-- | The opposite graph (with all edges reversed).

transpose :: (Ord s, Ord t) => Graph s t e -> Graph t s e
transpose = fromList . map transposeEdge . edges

-- * Graph deconstruction.

-- | Auxiliary function to turn empty map into @Nothing@.

discardEmpty :: Map k v -> Maybe (Map k v)
discardEmpty m = if Map.null m then Nothing else Just m

-- | Removes the given source node, and all corresponding edges, from the graph.
--
--   O(log n).
removeSourceNode :: Ord s => s -> Graph s t e -> Graph s t e
removeSourceNode s (Graph g) = Graph $ Map.delete s g

-- | Removes the given target node, and all corresponding edges, from the graph.
--
--   Expensive!  @O(n log n)@.

removeTargetNode :: (Ord s, Ord t) => t -> Graph s t e -> Graph s t e
removeTargetNode t (Graph g) = Graph $ Map.mapMaybe rem g
  where rem = discardEmpty . Map.delete t

-- | Removes the given node, be it source or target,
--   and all corresponding edges, from the graph.
--
--   Expensive!  @O(n log n)@.

removeNode :: Ord n => n -> Graph n n e -> Graph n n e
removeNode n = removeTargetNode n . removeSourceNode n

-- | @removeEdge s t g@ removes the edge going from @s@ to @t@, if any.
--
--   @O((log n)^2)@.

removeEdge :: (Ord s, Ord t) => s -> t -> Graph s t e -> Graph s t e
removeEdge s t (Graph g) = Graph $ Map.adjust (Map.delete t) s g

-- | Keep only the edges that satisfy the predicate.  @O(e).@

filterEdges :: (Ord s, Ord t) => (e -> Bool) -> Graph s t e -> Graph s t e
filterEdges f (Graph g) = Graph $ Map.mapMaybe (discardEmpty . Map.filter f) g

-- | Unzipping a graph (naive implementation using fmap).

unzip :: Graph s t (e, e') -> (Graph s t e, Graph s t e')
unzip g = (fst <$> g, snd <$> g)

-- * Strongly connected components.

-- | The graph's strongly connected components, in reverse topological
-- order.

sccs' :: Ord n => Graph n n e -> [Graph.SCC n]
sccs' (Graph g) =
  Graph.stronglyConnComp [ (n, n, Map.keys m) | (n, m) <- Map.assocs g ]

-- | The graph's strongly connected components, in reverse topological
-- order.

sccs :: Ord n => Graph n n e -> [[n]]
sccs = map Graph.flattenSCC . sccs'

-- | Returns @True@ iff the graph is acyclic.

acyclic :: Ord n => Graph n n e -> Bool
acyclic = all isAcyclic . sccs'
  where
  isAcyclic Graph.AcyclicSCC{} = True
  isAcyclic Graph.CyclicSCC{}  = False

-- * Graph composition

-- | @composeWith times plus g g'@ finds all edges
--   @s --c_i--> t_i --d_i--> u@ and constructs the
--   result graph from @edge(s,u) = sum_i (c_i times d_i)@.
--
--   Complexity:  for each edge @s --> t@ in @g@ we lookup up
--   all edges starting in with @t@ in @g'@.
--
composeWith :: (Ord s, Ord t, Ord u) => (c -> d -> e) -> (e -> e -> e) ->
  Graph s t c -> Graph t u d -> Graph s u e
composeWith times plus (Graph g) (Graph g') = Graph $
  Map.mapMaybe (discardEmpty . comp) g where
    comp m = Map.fromListWith plus
      [ (u, c `times` d)
      | (t, c) <- Map.assocs m
      , m'     <- maybeToList (Map.lookup t g')
      , (u, d) <- Map.assocs m'
      ]

-- | Computes the transitive closure of the graph.
--
-- Note that this algorithm is not guaranteed to be correct (or
-- terminate) for arbitrary semirings.
--
-- This function operates on the entire graph at once.

transitiveClosure1 :: (Eq e, SemiRing e, Ord n) =>
                      Graph n n e -> Graph n n e
transitiveClosure1 = completeUntilWith (==) otimes oplus
{-
 iterateUntil (==) growGraph  where

  -- @growGraph g@ unions @g@ with @(s --> t) `compose` g@ for each
  -- edge @s --> t@ in @g@
  growGraph g = List.foldl' (unionWith oplus) g $ for (edges g) $ \ (Edge s t e) ->
    case Map.lookup t (graph g) of
      Just es -> Graph $ Map.singleton s $ Map.map (otimes e) es
      Nothing -> empty
-}

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
      Nothing -> empty

-- | Computes the transitive closure of the graph.
--
-- Note that this algorithm is not guaranteed to be correct (or
-- terminate) for arbitrary semirings.
--
-- This function operates on one strongly connected component (SCC)
-- at a time.
--
-- For each SCC, it uses a saturation algorithm on state @(g, es)@
-- where initially @es@ is the set of edges of the SCC and @g@ the graph.
-- The algorithm finishes if @es@ has not changed in an iteration.
-- At each step, all @es@ are composed with @g@, the resulting
-- new graphs are unioned with @g@.  The new @es@ is then computed
-- as the edges of the SCC in the new @g@.

transitiveClosure :: (Eq e, SemiRing e, Ord n) => Graph n n e -> Graph n n e
transitiveClosure g = List.foldl' extend g $ sccs' g
  where
  -- extend the graph by new edges generated from a scc
  -- until there are no
  extend g (Graph.AcyclicSCC scc) = fst $ growGraph [scc] (edgesFrom' [scc] g)
  extend g (Graph.CyclicSCC  scc) = fst $
    iterateUntil ((==) `on` snd) (growGraph scc) (edgesFrom' scc g)

  edgesFrom' ns g = (g, edgesFrom g ns)

  growGraph scc (g, es) = edgesFrom' scc $
    -- the new graph:
    List.foldl' (unionWith oplus) g $ for es $ \ (Edge s t e) ->
      case Map.lookup t (graph g) of
        Just es -> Graph $ Map.singleton s $ Map.map (e `otimes`) es
        Nothing -> empty

-- | Correctness of the optimized algorithm that proceeds by SCC.

prop_transitiveClosure :: (Eq e, SemiRing e, Ord n) => Graph n n e -> Property
prop_transitiveClosure g = QuickCheck.label sccInfo $
  transitiveClosure g == transitiveClosure1 g
  where
  sccInfo =
    (if noSCCs <= 3 then "   " ++ show noSCCs
                    else ">= 4") ++
    " strongly connected component(s)"
    where noSCCs = length (sccs g)

-- | Find a path from a source node to a target node.
--
--   The path must satisfy the given predicate @good :: e -> Bool@.
findPath :: (SemiRing e, Ord n) => (e -> Bool) -> n -> n -> Graph n n e -> Maybe e
findPath good a b g = headMaybe $ filter good $ allPaths good a b g

-- | @allPaths classify a b g@ returns a list of pathes (accumulated edge weights)
--   from node @a@ to node @b@ in @g@.
--   Alternative intermediate pathes are only considered if they
--   are distinguished by the @classify@ function.
allPaths :: (SemiRing e, Ord n, Ord c) => (e -> c) -> n -> n -> Graph n n e -> [e]
allPaths classify s t g = paths Set.empty s
  where
    paths visited s = do
      (s', e) <- neighbours s g
      let tag     = (s', classify e)
          recurse = map (e `otimes`) (paths (Set.insert tag visited) s')
      if tag `Set.member` visited then []
      else if s' == t then e : recurse
      else recurse


------------------------------------------------------------------------
-- Utilities used to test the code above

instance (Arbitrary s, Arbitrary t, Arbitrary e) => Arbitrary (Edge s t e) where
  arbitrary = Edge <$> arbitrary <*> arbitrary <*> arbitrary

instance (CoArbitrary s, CoArbitrary t, CoArbitrary e) => CoArbitrary (Edge s t e) where
  coarbitrary (Edge s t e) = coarbitrary s . coarbitrary t . coarbitrary e

instance (Ord n, SemiRing e, Arbitrary n, Arbitrary e) =>
         Arbitrary (Graph n n e) where
  arbitrary = do
    nodes <- sized $ \ n -> resize (isqrt n) arbitrary
    edges <- mapM (\ (n1, n2) -> Edge n1 n2 <$> arbitrary) =<<
                  listOfElements ((,) <$> nodes <*> nodes)
    return (fromList edges `union` fromNodes nodes)
    where
    isqrt :: Int -> Int
    isqrt = round . sqrt . fromIntegral

  shrink g =
    [ removeNode n g     | n <- Set.toList $ nodes g ] ++
    [ removeEdge n1 n2 g | Edge n1 n2 _ <- edges g ]

-- | Generates a node from the graph. (Unless the graph is empty.)

nodeIn :: (Ord n, Arbitrary n) => Graph n n e -> Gen n
nodeIn g = elementsUnlessEmpty (Set.toList $ nodes g)

-- | Generates an edge from the graph. (Unless the graph contains no
-- edges.)

edgeIn :: (Ord n, Arbitrary n, Arbitrary e) =>
          Graph n n e -> Gen (Edge n n e)
edgeIn g = elementsUnlessEmpty (edges g)

-- | Sample graph type used to test 'transitiveClosure' and 'transitiveClosure1'.

type G = Graph N N E

-- | Sample node type used to test 'transitiveClosure' and 'transitiveClosure1'.

newtype N = N (Positive Int)
  deriving (Arbitrary, Eq, Ord)

n :: Int -> N
n = N . Positive

instance Show N where
  show (N (Positive n)) = "n " ++ show n

-- | Sample edge type used to test 'transitiveClosure' and 'transitiveClosure1'.

newtype E = E Bool
  deriving (Arbitrary, Eq, Show)

-- instance Show E where
--   show = show . unE

instance SemiRing E where
  oplus  (E x) (E y) = E (x || y)
  otimes (E x) (E y) = E (x && y)

-- | All tests.

tests :: IO Bool
tests = runTests "Agda.Utils.Graph.AdjacencyMap.Unidirectional"
  -- Other properties.
  [ quickCheck' (prop_nodes_fromNodes :: [Int] -> Bool)
  , quickCheck' (prop_transitiveClosure :: G -> Property)
  ]

