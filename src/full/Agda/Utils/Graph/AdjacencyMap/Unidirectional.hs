{-# LANGUAGE BangPatterns               #-}
{-# LANGUAGE CPP                        #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}

-- | Directed graphs (can of course simulate undirected graphs).
--
--   Represented as adjacency maps in direction from source to target.
--
--   Each source node maps to a adjacency map of outgoing edges,
--   which is a map from target nodes to edges.
--
--   This allows to get outgoing edges in O(log n) time where
--   @n@ is the number of nodes in the graph.
--
--   However, the set of incoming edges can only be obtained in
--   @O(n log n)@ or @O(e)@ where @e@ is the total number of edges.

module Agda.Utils.Graph.AdjacencyMap.Unidirectional
  ( Graph(..)
  , Edge(..)
  , transposeEdge
  , edges
  , edgesFrom
  , edgesTo
  , diagonal
  , lookup
  , neighbours, neighboursMap
  , sourceNodes, targetNodes
  , Nodes(..)
  , computeNodes, nodes
  , fromNodes
  , fromList, fromListWith
  , toList
  , discrete
  , clean
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
  , mapWithEdge
  , sccs'
  , sccs
  , DAG(..)
  , dagInvariant
  , oppositeDAG
  , reachable
  , sccDAG'
  , sccDAG
  , acyclic
  , reachableFrom
  , walkSatisfying
  , composeWith
  , complete
  , gaussJordanFloydWarshallMcNaughtonYamadaReference
  , gaussJordanFloydWarshallMcNaughtonYamada
  )
  where

import Prelude hiding (lookup, unzip, null)

import Control.Applicative hiding (empty)
import Control.Monad

import qualified Data.Array.IArray as Array
import qualified Data.Edison.Seq.BankersQueue as BQ
import qualified Data.Edison.Seq.SimpleQueue as SQ
import Data.Function
import qualified Data.Graph as Graph
import Data.IntMap.Strict (IntMap)
import qualified Data.IntMap.Strict as IntMap
import qualified Data.IntSet as IntSet
import qualified Data.List as List
import qualified Data.Map.Strict as Map
import Data.Map.Strict (Map)
import qualified Data.Maybe as Maybe
import Data.Maybe (maybeToList, fromMaybe, catMaybes)
import qualified Data.Set as Set
import Data.Set (Set)
import qualified Data.Tree as Tree

import Agda.Utils.Function
import Agda.Utils.Functor
import Agda.Utils.List (headMaybe)
import Agda.Utils.Null (Null(null))
import qualified Agda.Utils.Null as Null
import Agda.Utils.Pretty
import Agda.Utils.SemiRing
import Agda.Utils.Singleton (Singleton)
import qualified Agda.Utils.Singleton as Singleton
import Agda.Utils.Tuple

#include "undefined.h"
import Agda.Utils.Impossible

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
--
--   Incoming edges can only be computed in @O(n + e)@ time where
--   @e@ is the number of edges.

newtype Graph s t e = Graph
  { graph :: Map s (Map t e) -- ^ Forward edges.
  }
  deriving (Eq, Functor, Show)

instance (Pretty s, Pretty t, Pretty e) => Pretty (Graph s t e) where
  pretty = vcat . map pretty . edges

data Edge s t e = Edge
  { source :: s  -- ^ Outgoing node.
  , target :: t  -- ^ Incoming node.
  , label  :: e  -- ^ Edge label (weight).
  } deriving (Eq, Ord, Functor, Show)

instance (Pretty s, Pretty t, Pretty e) => Pretty (Edge s t e) where
  pretty (Edge s t e) = pretty s <+> text "--(" <> pretty t <> text ")-->" <+> pretty t

-- | Reverse an edge.

transposeEdge :: Edge s t e -> Edge t s e
transposeEdge (Edge s t e) = Edge t s e

-- * Edge queries

-- | Turn a graph into a list of edges.  @O(n + e)@

edges :: Graph s t e -> [Edge s t e]
edges (Graph g) =
  [ Edge s t e
  | (s, tes) <- Map.assocs g
  , (t, e)   <- Map.assocs tes
  ]

-- | All edges originating in the given nodes.
--   (I.e., all outgoing edges for the given nodes.)
--
--   Roughly linear in the length of the result list @O(result)@.

edgesFrom :: Ord s => Graph s t e -> [s] -> [Edge s t e]
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

edgesTo :: Ord t => Graph s t e -> [t] -> [Edge s t e]
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

neighbours :: Ord s => s -> Graph s t e -> [(t, e)]
neighbours s (Graph g) = maybe [] Map.assocs $ Map.lookup s g

-- | Get a list of outgoing edges with target.

neighboursMap :: Ord s => s -> Graph s t e -> Map t e
neighboursMap s (Graph g) = fromMaybe Map.empty $ Map.lookup s g

-- * Node queries

-- | Returns all the nodes with outgoing edges.  @O(n)@.

sourceNodes :: Graph s t e -> Set s
sourceNodes = Map.keysSet . graph

-- | Returns all the nodes with incoming edges.  Expensive! @O(e)@.

targetNodes :: Ord t => Graph s t e -> Set t
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

toList :: Graph s t e -> [Edge s t e]
toList (Graph g) = [ Edge s t a | (s,m) <- Map.assocs g, (t,a) <- Map.assocs m ]

-- | Check whether the graph is discrete (no edges).
--   This could be seen as an empty graph.
--   Worst-case (is discrete): @O(e)@.
discrete :: Null e => Graph s t e -> Bool
discrete = all' (all' null) . graph
  where all' p = List.all p . Map.elems

-- | Removes 'Null' edges (and empty 'Map's).
clean :: Null e => Graph s t e -> Graph s t e
clean = Graph . filt . fmap filt . graph
  where
    filt :: Null a => Map k a -> Map k a
    filt = Map.filter (not . null)

-- | Empty graph (no nodes, no edges).

empty :: Graph s t e
empty = Graph Map.empty

-- | A graph with two nodes and a single connecting edge.

singleton :: s -> t -> e -> Graph s t e
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

removeTargetNode :: Ord t => t -> Graph s t e -> Graph s t e
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

filterEdges :: (e -> Bool) -> Graph s t e -> Graph s t e
filterEdges f (Graph g) = Graph $ Map.mapMaybe (discardEmpty . Map.filter f) g

-- | Unzipping a graph (naive implementation using fmap).

unzip :: Graph s t (e, e') -> (Graph s t e, Graph s t e')
unzip g = (fst <$> g, snd <$> g)

-- | Maps over a graph under availability of positional information,
--   like 'Map.mapWithKey'.

mapWithEdge :: (Edge s t e -> e') -> Graph s t e -> Graph s t e'
mapWithEdge f (Graph g) = Graph $ flip Map.mapWithKey g $ \ s m ->
  flip Map.mapWithKey m $ \ t e -> f (Edge s t e)

-- * Strongly connected components.

-- | The graph's strongly connected components, in reverse topological
-- order.

sccs' :: Ord n => Graph n n e -> [Graph.SCC n]
sccs' g =
  Graph.stronglyConnComp
    [ (n, n, map target (edgesFrom g [n]))
    | n <- Set.toList (nodes g)
    ]

-- | The graph's strongly connected components, in reverse topological
-- order.

sccs :: Ord n => Graph n n e -> [[n]]
sccs = map Graph.flattenSCC . sccs'

-- | SCC DAGs.
--
-- The maps map SCC indices to and from SCCs/nodes.

data DAG n = DAG
  { dagGraph        :: Graph.Graph
  , dagComponentMap :: IntMap (Graph.SCC n)
  , dagNodeMap      :: Map n Int
  }

-- | 'DAG' invariant.

dagInvariant :: Ord n => DAG n -> Bool
dagInvariant g =
  Set.fromList (concatMap Graph.flattenSCC
                          (IntMap.elems (dagComponentMap g)))
    ==
  Map.keysSet (dagNodeMap g)
    &&
  IntSet.fromList (Map.elems (dagNodeMap g))
    ==
  IntMap.keysSet (dagComponentMap g)
    &&
  and [ n `elem` Graph.flattenSCC
                   (dagComponentMap g IntMap.! (dagNodeMap g Map.! n))
      | n <- Map.keys (dagNodeMap g)
      ]
    &&
  and [ dagNodeMap g Map.! n == i
      | i <- Graph.vertices (dagGraph g)
      , n <- Graph.flattenSCC (dagComponentMap g IntMap.! i)
      ]
    &&
  IntSet.fromList (Graph.vertices (dagGraph g))
    ==
  IntMap.keysSet (dagComponentMap g)
    &&
  all isAcyclic (Graph.scc (dagGraph g))
  where
  isAcyclic (Tree.Node r []) = not (r `elem` (dagGraph g Array.! r))
  isAcyclic _                = False

-- | The opposite DAG.

oppositeDAG :: DAG n -> DAG n
oppositeDAG g = g { dagGraph = Graph.transposeG (dagGraph g) }

-- | The nodes reachable from the given SCC.

reachable :: Ord n => DAG n -> Graph.SCC n -> [n]
reachable g scc = case scc of
  Graph.AcyclicSCC n      -> List.delete n (reachable' n)
  Graph.CyclicSCC (n : _) -> reachable' n
  Graph.CyclicSCC []      -> __IMPOSSIBLE__
  where
  lookup' g k = case IntMap.lookup k g of
    Nothing -> __IMPOSSIBLE__
    Just x  -> x

  lookup'' g k = case Map.lookup k g of
    Nothing -> __IMPOSSIBLE__
    Just x  -> x

  reachable' n =
    concatMap (Graph.flattenSCC . lookup' (dagComponentMap g)) $
    Graph.reachable (dagGraph g) (lookup'' (dagNodeMap g) n)

-- | Constructs a DAG containing the graph's strongly connected
-- components.

sccDAG' ::
  forall n e. Ord n
  => Graph n n e
  -> [Graph.SCC n]
     -- ^ The graph's strongly connected components.
  -> DAG n
sccDAG' g sccs = DAG theDAG componentMap secondNodeMap
  where
  components :: [(Int, Graph.SCC n)]
  components = zip [1..] sccs

  firstNodeMap :: Map n Int
  firstNodeMap = Map.fromList
    [ (n, i)
    | (i, c) <- components
    , n      <- Graph.flattenSCC c
    ]

  targets :: Int -> [n] -> [Int]
  targets i ns =
    IntSet.toList $ IntSet.fromList
      [ j
      | e <- edgesFrom g ns
      , let j = case Map.lookup (target e) firstNodeMap of
                  Nothing -> __IMPOSSIBLE__
                  Just j  -> j
      , j /= i
      ]

  (theDAG, _, toVertex) =
    Graph.graphFromEdges
      [ (i, i, targets i (Graph.flattenSCC c))
      | (i, c) <- components
      ]

  convertInt :: Int -> Graph.Vertex
  convertInt i = case toVertex i of
    Nothing -> __IMPOSSIBLE__
    Just i  -> i

  componentMap :: IntMap (Graph.SCC n)
  componentMap = IntMap.fromList (map (mapFst convertInt) components)

  secondNodeMap :: Map n Int
  secondNodeMap = fmap convertInt firstNodeMap

-- | Constructs a DAG containing the graph's strongly connected
-- components.

sccDAG :: Ord n => Graph n n e -> DAG n
sccDAG g = sccDAG' g (sccs' g)

-- | Returns @True@ iff the graph is acyclic.

acyclic :: Ord n => Graph n n e -> Bool
acyclic = all isAcyclic . sccs'
  where
  isAcyclic Graph.AcyclicSCC{} = True
  isAcyclic Graph.CyclicSCC{}  = False

-- | @reachableFrom g n@ is a map containing all nodes reachable from
-- @n@ in @g@. For each node a simple path to the node is given, along
-- with its length (the number of edges). The paths are as short as
-- possible (in terms of the number of edges).
--
-- Precondition: @n@ must be a node in @g@. The number of nodes in the
-- graph must not be larger than @'maxBound' :: 'Int'@.
--
-- Amortised time complexity (assuming that comparisons take constant
-- time): /O(e log n)/, if the lists are not inspected. Inspection of
-- a prefix of a list is linear in the length of the prefix.

reachableFrom :: Ord n => Graph n n e -> n -> Map n (Int, [Edge n n e])
reachableFrom g n = bfs (SQ.singleton (n, BQ.empty)) Map.empty
  where
  bfs !q !map = case SQ.lview q of
    Nothing          -> map
    Just ((u, p), q) ->
      if u `Map.member` map
      then bfs q map
      else bfs (foldr SQ.rcons q
                      [ (v, BQ.rcons (Edge u v e) p)
                      | (v, e) <- neighbours u g
                      ])
               (let n = BQ.size p in
                n `seq` Map.insert u (n, BQ.toList p) map)

-- | @walkSatisfying every some g from to@ determines if there is a
-- walk from @from@ to @to@ in @g@, in which every edge satisfies the
-- predicate @every@, and some edge satisfies the predicate @some@. If
-- there are several such walks, then a shortest one (in terms of the
-- number of edges) is returned.
--
-- Precondition: @from@ and @to@ must be nodes in @g@. The number of
-- nodes in the graph must not be larger than @'maxBound' :: 'Int'@.
--
-- Amortised time complexity (assuming that comparisons and the
-- predicates take constant time to compute): /O(e log n)/.

walkSatisfying ::
  Ord n =>
  (e -> Bool) -> (e -> Bool) ->
  Graph n n e -> n -> n -> Maybe [Edge n n e]
walkSatisfying every some g from to =
  case
    [ (l1 + l2, p1 ++ [e] ++ map transposeEdge (reverse p2))
    | e <- everyEdges
    , some (label e)
    , (l1, p1) <- maybeToList (Map.lookup (source e) fromReaches)
    , (l2, p2) <- maybeToList (Map.lookup (target e) reachesTo)
    ] of
    []  -> Nothing
    ess -> Just $ snd $ List.minimumBy (compare `on` fst) ess
  where
  everyEdges = [ e | e <- toList g, every (label e) ]

  fromReaches = reachableFrom (fromList everyEdges) from

  reachesTo =
    reachableFrom (fromList (map transposeEdge everyEdges)) to

-- * Graph composition

-- | @composeWith times plus g g'@ finds all edges
--   @s --c_i--> t_i --d_i--> u@ and constructs the
--   result graph from @edge(s,u) = sum_i (c_i times d_i)@.
--
--   Complexity:  for each edge @s --> t@ in @g@ we lookup up
--   all edges starting in with @t@ in @g'@.
--
composeWith :: (Ord t, Ord u) => (c -> d -> e) -> (e -> e -> e) ->
  Graph s t c -> Graph t u d -> Graph s u e
composeWith times plus (Graph g) (Graph g') = Graph $
  Map.mapMaybe (discardEmpty . comp) g where
    comp m = Map.fromListWith plus
      [ (u, c `times` d)
      | (t, c) <- Map.assocs m
      , m'     <- maybeToList (Map.lookup t g')
      , (u, d) <- Map.assocs m'
      ]

-- | Transitive closure ported from "Agda.Termination.CallGraph".
--
--   Relatively efficient, see Issue 1560.

complete :: (Eq e, Null e, SemiRing e, Ord n) => Graph n n e -> Graph n n e
complete g = repeatWhile (mapFst (not . discrete) . combineNewOld' g) g
  where
    combineNewOld' new old = unzip $ unionWith comb new' old'
      where
      -- The following procedure allows us to check if anything new happened:
      -- Pair the composed graphs with an empty graph.
      -- The empty graph will remain empty.  We only need it due to the typing
      -- of Map.unionWith.
      new' = (,Null.empty) <$> composeWith otimes oplus new old
      -- Pair an empty graph with the old graph.
      old' = (Null.empty,) <$> old
      -- Combine the pairs.
      -- Update 'old' with 'new'.  This will be the new 'old'. No new 'new' if no change.
      comb (new, _) (_, old) = (if x == old then Null.empty else x, x)
        where x = old `oplus` new

-- | Version of 'complete' that produces a list of intermediate results
--   paired to the left with a difference that lead to the new intermediat result.
--
--   The last element in the list is the transitive closure, paired with the empty graph.
--
--   @complete g = snd $ last $ completeIter g@

completeIter :: (Eq e, Null e, SemiRing e, Ord n) => Graph n n e -> [(Graph n n e, Graph n n e)]
completeIter g = iterWhile (not . discrete) (combineNewOld' g) g
  where
    combineNewOld' new old = unzip $ unionWith comb new' old'
      where
      -- The following procedure allows us to check if anything new happened:
      -- Pair the composed graphs with an empty graph.
      -- The empty graph will remain empty.  We only need it due to the typing
      -- of Map.unionWith.
      new' = (,Null.empty) <$> composeWith otimes oplus new old
      -- Pair an empty graph with the old graph.
      old' = (Null.empty,) <$> old
      -- Combine the pairs.
      -- Update 'old' with 'new'.  This will be the new 'old'. No new 'new' if no change.
      comb (new, _) (_, old) = (if x == old then Null.empty else x, x)
        where x = old `oplus` new

-- | Computes the transitive closure of the graph.
--
-- Uses the Gauss-Jordan-Floyd-Warshall-McNaughton-Yamada algorithm
-- (as described by Russell O'Connor in \"A Very General Method of
-- Computing Shortest Paths\"
-- <http://r6.ca/blog/20110808T035622Z.html>), implemented using
-- matrices.
--
-- The resulting graph does not contain any zero edges.
--
-- This algorithm should be seen as a reference implementation. In
-- practice 'gaussJordanFloydWarshallMcNaughtonYamada' is likely to be
-- more efficient.

gaussJordanFloydWarshallMcNaughtonYamadaReference ::
  forall n e. (Ord n, Eq e, StarSemiRing e) =>
  Graph n n e -> Graph n n e
gaussJordanFloydWarshallMcNaughtonYamadaReference g =
  toGraph (foldr step initialMatrix nodeIndices)
  where
  indicesAndNodes = zip [1..] $ Set.toList $ nodes g
  nodeMap         = Map.fromList $ map swap indicesAndNodes
  indexMap        = Map.fromList            indicesAndNodes

  noNodes      = Map.size nodeMap
  nodeIndices  = [1 .. noNodes]
  matrixBounds = ((1, 1), (noNodes, noNodes))

  initialMatrix :: Array.Array (Int, Int) e
  initialMatrix =
    Array.accumArray
      oplus ozero
      matrixBounds
      [ ((nodeMap Map.! source e, nodeMap Map.! target e), label e)
      | e <- edges g
      ]

  rightStrictPair i !e = (i , e)

  step k !m =
    Array.array
      matrixBounds
      [ rightStrictPair
          (i, j)
          (oplus (m Array.! (i, j))
                 (otimes (m Array.! (i, k))
                         (otimes (ostar (m Array.! (k, k)))
                                 (m Array.! (k, j)))))
      | i <- nodeIndices, j <- nodeIndices
      ]

  toGraph m =
    fromList [ Edge (indexMap Map.! i) (indexMap Map.! j) e
             | ((i, j), e) <- Array.assocs m
             , e /= ozero
             ]

-- | Computes the transitive closure of the graph.
--
-- Uses the Gauss-Jordan-Floyd-Warshall-McNaughton-Yamada algorithm
-- (as described by Russell O'Connor in \"A Very General Method of
-- Computing Shortest Paths\"
-- <http://r6.ca/blog/20110808T035622Z.html>), implemented using
-- 'Graph', and with some shortcuts:
--
-- * Zero edge differences are not added to the graph, thus avoiding
--   some zero edges.
--
-- * Strongly connected components are used to avoid computing some
--   zero edges.
--
-- The graph's strongly connected components (in reverse topological
-- order) are returned along with the transitive closure.

gaussJordanFloydWarshallMcNaughtonYamada ::
  forall n e. (Ord n, Eq e, StarSemiRing e) =>
  Graph n n e -> (Graph n n e, [Graph.SCC n])
gaussJordanFloydWarshallMcNaughtonYamada g =
  (loop components g, components)
  where
  components = sccs' g
  forwardDAG = sccDAG' g components
  reverseDAG = oppositeDAG forwardDAG

  loop :: [Graph.SCC n] -> Graph n n e -> Graph n n e
  loop []           !g = g
  loop (scc : sccs)  g =
    loop sccs (foldr step g (Graph.flattenSCC scc))
    where
    -- All nodes that are reachable from the SCC.
    canBeReached = reachable forwardDAG scc
    -- All nodes that can reach the SCC.
    canReach     = reachable reverseDAG scc

    step :: n -> Graph n n e -> Graph n n e
    step k !g =
      foldr (insertEdgeWith oplus) g
        [ Edge i j e
        | i <- canReach
        , j <- canBeReached
        , let e = otimes (lookup' i k) (starTimes (lookup' k j))
        , e /= ozero
        ]
      where
      starTimes = otimes (ostar (lookup' k k))

      lookup' s t = case lookup s t g of
        Nothing -> ozero
        Just e  -> e
