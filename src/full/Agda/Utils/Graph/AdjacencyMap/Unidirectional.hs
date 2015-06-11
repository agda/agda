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
  , neighbours
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
  , sccs'
  , sccs
  , acyclic
  , composeWith
  , complete
  , transitiveClosure
  , findPath
  , allPaths
  )
  where

import Prelude hiding (lookup, unzip, null)

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

import Agda.Utils.Function (iterateUntil, repeatWhile)
import Agda.Utils.Functor (for)
import Agda.Utils.List (headMaybe)
import Agda.Utils.Null (Null(null))
import qualified Agda.Utils.Null as Null
import Agda.Utils.SemiRing
import Agda.Utils.Tuple

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

-- -- | Transitive closure ported from "Agda.Termination.CallGraph".
-- complete :: (Eq e, Null e, SemiRing e, Ord n) => Graph n n e -> Graph n n e
-- complete g = repeatWhile (mapFst (not . discrete) . combineNewOld' g) g
--   where
--     combineNewOld' new old = unzip $ unionWith comb new' old'
--       where
--       new' = (,Null.empty) <$> composeWith otimes oplus new old
--       old' = (Null.empty,) <$> old
--       comb (new1,old1) (new2,old2)  -- TODO: ensure old1 is null
--         = mapFst (new2 `oplus`) $ combineNewOld'' new1 old2
--       combineNewOld'' new old = (new', old')
--         where
--           -- update old
--           old' = old `oplus` new
--           -- if no change, then nothing new
--           new' = if old' == old then Null.empty else old'

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
--
-- NOTE: this algorithm is INEFFICIENT, see Issue 1560.

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
