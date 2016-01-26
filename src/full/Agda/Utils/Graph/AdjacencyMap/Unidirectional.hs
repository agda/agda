{-# LANGUAGE BangPatterns               #-}
{-# LANGUAGE CPP                        #-}
{-# LANGUAGE DeriveFunctor              #-}
{-# LANGUAGE DoAndIfThenElse            #-}
{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE ScopedTypeVariables        #-}
{-# LANGUAGE TupleSections              #-}

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
  , composeWith
  , complete
  , gaussJordanFloydWarshallMcNaughtonYamadaReference
  , gaussJordanFloydWarshallMcNaughtonYamada
  , findPath
  , allPaths
  -- , allTrails  -- Exponential, don't use!  See issue 1612.
  )
  where

import Prelude hiding (lookup, unzip, null)

import Control.Applicative hiding (empty)
import Control.Monad

import qualified Data.Array.IArray as Array
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

import Test.QuickCheck hiding (label)

import Agda.Utils.Function
import Agda.Utils.Functor
import Agda.Utils.List (headMaybe)
import Agda.Utils.Null (Null(null))
import qualified Agda.Utils.Null as Null
import Agda.Utils.SemiRing
import Agda.Utils.Singleton (Singleton)
import qualified Agda.Utils.Singleton as Singleton
import Agda.Utils.TestHelpers
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

-- | Remove 'Null' edges.
clean :: (Ord s, Ord t, Null e) => Graph s t e -> Graph s t e
clean = Graph . filt . fmap filt . graph
  where
    filt :: (Ord k, Null a) => Map k a -> Map k a
    filt = Map.fromAscList . List.filter (not . null . snd) . Map.toAscList

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

gaussJordanFloydWarshallMcNaughtonYamada ::
  forall n e. (Ord n, Eq e, StarSemiRing e) =>
  Graph n n e -> Graph n n e
gaussJordanFloydWarshallMcNaughtonYamada g = loop components g
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

-- THE FOLLOWING IMPLEMENTATION OF allTrails is in practice worse
-- then the naive depth-first search with backtracking.

-- -- | A trail is a non-empty list of consecutive edges with no duplicate.
-- --   We store a set of edges for more efficient trail composition.
-- --
-- --   Invariants for @Trail tr s@:
-- --
-- --   1. nonempty
-- --   @not $ null tr@.
-- --
-- --   2. consecutive
-- --   @List.and $ zipWith (\ (Edge _ t1 _) (Edge s2 _ _) -> t1 == s2) tr (tail tr)@.
-- --
-- --   3. coherence
-- --   @Set.toAscList s == sort $ map (\ (Edges s t _) -> (s,t)) tr@.

-- data Trail n e = Trail { trail :: [Edge n n e], trailEdgeSet :: Set (n, n) }
--   deriving (Show)

-- instance (Eq n, Eq e) => Eq (Trail n e) where
--   (==) = (==) `on` trail

-- instance (Ord n, Ord e) => Ord (Trail n e) where
--   compare = compare `on` trail

-- singletonTrail :: Edge n n e -> Trail n e
-- singletonTrail e@(Edge s t _) = Trail [e] $ Set.singleton (s,t)

-- trailSource :: Trail n e -> n
-- trailSource (Trail (Edge s _ _ : _) _) = s
-- trailSource _ = __IMPOSSIBLE__

-- trailTarget :: Trail n e -> n
-- trailTarget (Trail (Edge _ t _ : _) _) = t
-- trailTarget _ = __IMPOSSIBLE__

-- -- | Precondition for @composeTrails t1 t2@:
-- --   @trailTarget t1 == trailSource t2@.
-- composeTrails :: (Ord n) => Trail n e -> Trail n e -> Maybe (Trail n e)
-- composeTrails (Trail t1 s1) (Trail t2 s2) =
--   if null (Set.intersection s1 s2) then Just $ Trail (t1 ++ t2) $ Set.union s1 s2
--   else Nothing

-- composeTrails_alt :: (Ord n) => Trail n e -> Trail n e -> Maybe (Trail n e)
-- composeTrails_alt t (Trail [] _) = Just t
-- composeTrails_alt (Trail [] _) t = Just t
-- composeTrails_alt (Trail t1 s1) (Trail t2 s2) =
--   foldr cons (return t2) t1 <&> \ t12 -> Trail t12 $ Set.union s1 s2
--   where
--     cons e@(Edge s t _) mt12 = do
--       t12 <- mt12
--       guard $ (s,t) `Set.notMember` s2
--       return $ e : t12

-- -- | A possibly empty set of trails with same source and same target.
-- --
-- --   Invariants for @Tails ts@:
-- --   Same source: @length (group (map trailSource ts)) == 1@.
-- --   Same target: @length (group (map trailTarget ts)) == 1@.

-- newtype Trails n e = Trails { trails :: Set (Trail n e) }
--   deriving (Eq, Ord, Show, Null, Singleton (Trail n e))

-- instance (Ord n, Ord e) => SemiRing (Trails n e) where
--   ozero = Null.empty
--   oone  = __IMPOSSIBLE__
--   oplus  (Trails t1s) (Trails t2s) = Trails $ Set.union t1s t2s
--   otimes (Trails t1s) (Trails t2s) = Trails $ Set.fromList $
--     catMaybes [ composeTrails t1 t2 | t1 <- Set.toList t1s, t2 <- Set.toList t2s ]

-- -- | We compute @allTrails@ by a transitive closure algorithm.
-- --   In practice, we are only interested in the first trail
-- --   with a specific property, so it is important
-- --   to compute @allTrails@ lazily.
-- --
-- --   We use a graph with edges labelled by 'Trails'.
-- allTrails :: forall e n. (Eq e, Ord e, SemiRing e, Ord n) =>
--   n -> n -> Graph n n e -> [e]
-- allTrails s t g = map collapse st
--   where
--     -- Construct a graph of singleton trails
--     init :: Graph n n (Trails n e)
--     init = mapWithEdge (Singleton.singleton . singletonTrail) g
--     -- Compute transitive closure iteratively and keep the diffs.
--     diffs = init : map fst (completeIter init)
--     -- Extract a sequence of trails from s to t from the diff sequence.
--     -- Each diff may contain several or no trails from s to t.
--     st    = concat $ map (maybe [] (Set.toList . trails) . lookup s t) diffs
--     -- Multiply the edge weights a long a trail.
--     collapse (Trail tr _) = foldr1 otimes $ map label tr

-- | @allTrails a b g@ returns all trails (walks where all edges are
-- distinct) from node @a@ to node @b@ in @g@. The trails are returned
-- in the form of accumulated edge weights.
--
-- This definition can perhaps be optimised through the use of
-- memoisation.
--
-- Andreas, 2015-07-21 Issue 1612: This function is worst-case exponential
-- as the @k@-complete graph has @k!@ many trails.  DON'T USE!

allTrails :: forall e n. (SemiRing e, Ord n) =>
             n -> n -> Graph n n e -> [e]
allTrails s t g = paths Set.empty s
  where
    paths :: Set (n, n) -> n -> [e]
    paths traversed s = do
      (s', e) <- neighbours s g
      let edge    = (s, s')
          recurse = (e `otimes`) <$> paths (Set.insert edge traversed) s'
      if edge `Set.member` traversed then []
      else if s' == t then e : recurse
      else recurse

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
