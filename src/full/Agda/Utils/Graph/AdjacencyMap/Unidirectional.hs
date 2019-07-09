{-# LANGUAGE BangPatterns               #-}

-- | Directed graphs (can of course simulate undirected graphs).
--
--   Represented as adjacency maps in direction from source to target.
--
--   Each source node maps to an adjacency map of outgoing edges,
--   which is a map from target nodes to edges.
--
--   Listed time complexities are for the worst case (and possibly
--   amortised), with /n/ standing for the number of nodes in the
--   graph and /e/ standing for the number of edges. Comparisons,
--   predicates etc. are assumed to take constant time (unless
--   otherwise stated).

module Agda.Utils.Graph.AdjacencyMap.Unidirectional
  ( -- * Graphs and edges
    Graph(..)
  , invariant
  , Edge(..)
    -- * Queries
  , lookup
  , edges
  , neighbours, neighboursMap
  , edgesFrom
  , edgesTo
  , diagonal
  , nodes, sourceNodes, targetNodes, isolatedNodes
  , Nodes(..), computeNodes
  , discrete
  , acyclic
    -- * Construction
  , fromNodes, fromNodeSet
  , fromEdges, fromEdgesWith
  , empty
  , singleton
  , insert, insertWith
  , insertEdge, insertEdgeWith
  , union, unionWith
  , unions, unionsWith
    -- * Transformation
  , mapWithEdge
  , transposeEdge, transpose
  , clean
  , removeNode, removeNodes
  , removeEdge
  , filterEdges
  , unzip
  , composeWith
    -- * Strongly connected components
  , sccs'
  , sccs
  , DAG(..)
  , dagInvariant
  , oppositeDAG
  , reachable
  , sccDAG'
  , sccDAG
    -- * Reachability
  , reachableFrom, reachableFromSet
  , walkSatisfying
    -- * Transitive closure
  , gaussJordanFloydWarshallMcNaughtonYamada
  , gaussJordanFloydWarshallMcNaughtonYamadaReference
  , complete, completeIter
  )
  where

import Prelude hiding ( lookup, null, unzip )

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
import Data.Maybe (maybeToList, fromMaybe)
import qualified Data.Set as Set
import Data.Set (Set)
import qualified Data.Tree as Tree

import Agda.Utils.Function
import Agda.Utils.Functor
import Agda.Utils.Null (Null(null))
import qualified Agda.Utils.Null as Null
import Agda.Utils.Pretty
import Agda.Utils.SemiRing
import qualified Agda.Utils.Singleton as Singleton
import Agda.Utils.Tuple

import Agda.Utils.Impossible

------------------------------------------------------------------------
-- Graphs and edges

-- | @Graph n e@ is a type of directed graphs with nodes in @n@ and
--   edges in @e@.
--
--   At most one edge is allowed between any two nodes. Multigraphs
--   can be simulated by letting the edge type @e@ be a collection
--   type.
--
--   The graphs are represented as adjacency maps (adjacency lists,
--   but using finite maps instead of arrays and lists). This makes it
--   possible to compute a node's outgoing edges in logarithmic time
--   (/O(log n)/). However, computing the incoming edges may be more
--   expensive.
--
--   Note that neither the number of nodes nor the number of edges may
--   exceed @'maxBound' :: 'Int'@.

newtype Graph n e = Graph
  { graph :: Map n (Map n e) -- ^ Forward edges.
  }
  deriving Eq

-- The Functor instance for strict maps is the one for lazy maps, so a
-- custom Functor instance using strict map functions is used here.

instance Functor (Graph n) where
  fmap f = Graph . Map.map (Map.map f) . graph

-- | Internal invariant.

invariant :: Ord n => Graph n e -> Bool
invariant g =
  -- Every target node must be present in the graph as a source node,
  -- possibly without outgoing edges.
  Set.isSubsetOf (targetNodes g) (nodes g)

instance (Ord n, Pretty n, Pretty e) => Pretty (Graph n e) where
  pretty g = vcat (concatMap pretty' (Set.toAscList (nodes g)))
    where
    pretty' n = case edgesFrom g [n] of
      [] -> [pretty n]
      es -> map pretty es

instance (Ord n, Show n, Show e) => Show (Graph n e) where
  showsPrec _ g =
    showString "union (fromEdges " .
    shows (edges g) .
    showString ") (fromNodes " .
    shows (Set.toList (isolatedNodes g)) .
    showString ")"

-- | Edges.

data Edge n e = Edge
  { source :: n  -- ^ Outgoing node.
  , target :: n  -- ^ Incoming node.
  , label  :: e  -- ^ Edge label (weight).
  } deriving (Eq, Ord, Functor, Show)

instance (Pretty n, Pretty e) => Pretty (Edge n e) where
  pretty (Edge s t e) =
    pretty s <+> ("--(" <> pretty e <> ")-->") <+> pretty t

------------------------------------------------------------------------
-- Queries

-- | If there is an edge from @s@ to @t@, then @lookup s t g@ is
-- @'Just' e@, where @e@ is the edge's label. /O(log n)/.

lookup :: Ord n => n -> n -> Graph n e -> Maybe e
lookup s t (Graph g) = Map.lookup t =<< Map.lookup s g

-- | The graph's edges. /O(n + e)/.

edges :: Graph n e -> [Edge n e]
edges (Graph g) =
  [ Edge s t e
  | (s, tes) <- Map.assocs g
  , (t, e)   <- Map.assocs tes
  ]

-- | @neighbours u g@ consists of all nodes @v@ for which there is an
-- edge from @u@ to @v@ in @g@, along with the corresponding edge
-- labels. /O(log n + |@neighbours u g@|)/.

neighbours :: Ord n => n -> Graph n e -> [(n, e)]
neighbours s = Map.toList . neighboursMap s

-- | @neighboursMap u g@ consists of all nodes @v@ for which there is
-- an edge from @u@ to @v@ in @g@, along with the corresponding edge
-- labels. /O(log n)/.

neighboursMap :: Ord n => n -> Graph n e -> Map n e
neighboursMap s (Graph g) = fromMaybe Map.empty $ Map.lookup s g

-- | @edgesFrom g ns@ is a list containing all edges originating in
-- the given nodes (i.e., all outgoing edges for the given nodes). If
-- @ns@ does not contain duplicates, then the resulting list does not
-- contain duplicates. /O(|@ns@| log |@n@| + |@edgesFrom g ns@|)/.

edgesFrom :: Ord n => Graph n e -> [n] -> [Edge n e]
edgesFrom (Graph g) ss =
  [ Edge s t e
  | s <- ss
  , m <- maybeToList $ Map.lookup s g
  , (t, e) <- Map.assocs m
  ]

-- | @edgesTo g ns@ is a list containing all edges ending in the given
-- nodes (i.e., all incoming edges for the given nodes). If @ns@ does
-- not contain duplicates, then the resulting list does not contain
-- duplicates. /O(|@ns@| n log n)/.

edgesTo :: Ord n => Graph n e -> [n] -> [Edge n e]
edgesTo (Graph g) ts =
  [ Edge s t e
  | (s, m) <- Map.assocs g
  , t <- ts
  , e <- maybeToList $ Map.lookup t m
  ]

-- | All self-loops. /O(n log n)/.

diagonal :: Ord n => Graph n e -> [Edge n e]
diagonal (Graph g) =
  [ Edge s s e
  | (s, m) <- Map.assocs g
  , e      <- maybeToList $ Map.lookup s m
  ]

-- | All nodes. /O(n)/.

nodes :: Graph n e -> Set n
nodes = Map.keysSet . graph

-- | Nodes with outgoing edges. /O(n)/.

sourceNodes :: Graph n e -> Set n
sourceNodes = Map.keysSet . Map.filter (not . Map.null) . graph

-- | Nodes with incoming edges. /O(n + e log n)/.

targetNodes :: Ord n => Graph n e -> Set n
targetNodes = Set.fromList . map target . edges

-- | Various kinds of nodes.

data Nodes n = Nodes
  { srcNodes :: Set n
    -- ^ Nodes with outgoing edges.
  , tgtNodes :: Set n
    -- ^ Nodes with incoming edges.
  , allNodes :: Set n
    -- ^ All nodes, with or without edges.
  }

-- | Constructs a 'Nodes' structure. /O(n + e log n)/.

computeNodes :: Ord n => Graph n e -> Nodes n
computeNodes g =
  Nodes { srcNodes = Set.filter (not . null . flip neighbours g) ns
        , tgtNodes = targetNodes g
        , allNodes = ns
        }
  where
  ns = nodes g

-- | Nodes without incoming or outgoing edges. /O(n + e log n)/.

isolatedNodes :: Ord n => Graph n e -> Set n
isolatedNodes g =
  Set.difference (allNodes ns) (Set.union (srcNodes ns) (tgtNodes ns))
  where
  ns = computeNodes g

-- | Checks whether the graph is discrete (containing no edges other
-- than 'null' edges). /O(n + e)/.

discrete :: Null e => Graph n e -> Bool
discrete = all' (all' null) . graph
  where all' p = List.all p . Map.elems

-- | Returns @True@ iff the graph is acyclic.

acyclic :: Ord n => Graph n e -> Bool
acyclic = all isAcyclic . sccs'
  where
  isAcyclic Graph.AcyclicSCC{} = True
  isAcyclic Graph.CyclicSCC{}  = False

------------------------------------------------------------------------
-- Construction

-- | Constructs a completely disconnected graph containing the given
--   nodes. /O(n log n)/.

fromNodes :: Ord n => [n] -> Graph n e
fromNodes ns = Graph $ Map.fromList $ map (, Map.empty) ns

-- | Constructs a completely disconnected graph containing the given
--   nodes. /O(n)/.

fromNodeSet :: Ord n => Set n -> Graph n e
fromNodeSet ns = Graph $ Map.fromSet (\_ -> Map.empty) ns

-- | @fromEdges es@ is a graph containing the edges in @es@, with the
-- caveat that later edges overwrite earlier edges. /O(|@es@| log n)/.

fromEdges :: Ord n => [Edge n e] -> Graph n e
fromEdges = fromEdgesWith $ \ new old -> new

-- | @fromEdgesWith f es@ is a graph containing the edges in @es@.
-- Later edges are combined with earlier edges using the supplied
-- function. /O(|@es@| log n)/.

fromEdgesWith :: Ord n => (e -> e -> e) -> [Edge n e] -> Graph n e
fromEdgesWith f = List.foldl' (flip (insertEdgeWith f)) empty

-- | Empty graph (no nodes, no edges). /O(1)/.

empty :: Graph n e
empty = Graph Map.empty

-- | A graph with two nodes and a single connecting edge. /O(1)/.

singleton :: Ord n => n -> n -> e -> Graph n e
singleton s t e = insert s t e empty

-- | Inserts an edge into the graph. /O(log n)/.

insert :: Ord n => n -> n -> e -> Graph n e -> Graph n e
insert = insertWith $ \ new old -> new

-- | Inserts an edge into the graph. /O(log n)/.

insertEdge :: Ord n => Edge n e -> Graph n e -> Graph n e
insertEdge (Edge s t e) = insert s t e

-- | @insertWith f s t new@ inserts an edge from @s@ to @t@ into the
-- graph. If there is already an edge from @s@ to @t@ with label @old@,
-- then this edge gets replaced by an edge with label @f new old@, and
-- otherwise the edge's label is @new@. /O(log n)/.

insertWith ::
  Ord n => (e -> e -> e) -> n -> n -> e -> Graph n e -> Graph n e
insertWith f s t e (Graph g) =
  Graph (Map.alter (Just . insNode) t $ Map.alter (Just . insEdge) s g)
  where
  insEdge Nothing  = Map.singleton t e
  insEdge (Just m) = Map.insertWith f t e m

  insNode Nothing  = Map.empty
  insNode (Just m) = m

-- | A variant of 'insertWith'. /O(log n)/.

insertEdgeWith ::
  Ord n => (e -> e -> e) -> Edge n e -> Graph n e -> Graph n e
insertEdgeWith f (Edge s t e) = insertWith f s t e

-- | Left-biased union.
--
-- Time complexity: See 'unionWith'.

union :: Ord n => Graph n e -> Graph n e -> Graph n e
union = unionWith $ \ left right -> left

-- | Union. The function is used to combine edge labels for edges that
-- occur in both graphs (labels from the first graph are given as the
-- first argument to the function).
--
-- Time complexity: /O(n₁ log (n₂/n₁ + 1) + e₁ log e₂/, where /n₁/ is
-- the number of nodes in the graph with the smallest number of nodes
-- and /n₂/ is the number of nodes in the other graph, and /e₁/ is the
-- number of edges in the graph with the smallest number of edges and
-- /e₂/ is the number of edges in the other graph.
--
-- Less complicated time complexity: /O((n + e) log n/ (where /n/ and
-- /e/ refer to the resulting graph).

unionWith ::
  Ord n => (e -> e -> e) -> Graph n e -> Graph n e -> Graph n e
unionWith f (Graph g) (Graph g') =
  Graph $ Map.unionWith (Map.unionWith f) g g'

-- | Union. /O((n + e) log n/ (where /n/ and /e/ refer to the
-- resulting graph).

unions :: Ord n => [Graph n e] -> Graph n e
unions = unionsWith $ \ left right -> left

-- | Union. The function is used to combine edge labels for edges that
-- occur in several graphs. /O((n + e) log n/ (where /n/ and /e/ refer
-- to the resulting graph).

unionsWith :: Ord n => (e -> e -> e) -> [Graph n e] -> Graph n e
unionsWith f = List.foldl' (unionWith f) empty

------------------------------------------------------------------------
-- Transformation

-- | A variant of 'fmap' that provides extra information to the
-- function argument. /O(n + e)/.

mapWithEdge :: (Edge n e -> e') -> Graph n e -> Graph n e'
mapWithEdge f (Graph g) = Graph $ flip Map.mapWithKey g $ \ s m ->
  flip Map.mapWithKey m $ \ t e -> f (Edge s t e)

-- | Reverses an edge. /O(1)/.

transposeEdge :: Edge n e -> Edge n e
transposeEdge (Edge s t e) = Edge t s e

-- | The opposite graph (with all edges reversed). /O((n + e) log n)/.

transpose :: Ord n => Graph n e -> Graph n e
transpose g =
  fromEdges (map transposeEdge (edges g))
    `union`
  fromNodeSet (isolatedNodes g)

-- | Removes 'null' edges. /O(n + e)/.

clean :: Null e => Graph n e -> Graph n e
clean = Graph . Map.map (Map.filter (not . null)) . graph

-- | @removeNodes ns g@ removes the nodes in @ns@ (and all
-- corresponding edges) from @g@. /O((n + e) log |@ns@|)/.

removeNodes :: Ord n => Set n -> Graph n e -> Graph n e
removeNodes ns (Graph g) = Graph (Map.mapMaybeWithKey remSrc g)
  where
  remSrc s m
    | Set.member s ns = Nothing
    | otherwise       =
        Just (Map.filterWithKey (\t _ -> not (Set.member t ns)) m)

-- | @removeNode n g@ removes the node @n@ (and all corresponding
-- edges) from @g@. /O(n + e)/.

removeNode :: Ord n => n -> Graph n e -> Graph n e
removeNode = removeNodes . Set.singleton

-- | @removeEdge s t g@ removes the edge going from @s@ to @t@, if any.
--   /O(log n)/.

removeEdge :: Ord n => n -> n -> Graph n e -> Graph n e
removeEdge s t (Graph g) = Graph $ Map.adjust (Map.delete t) s g

-- | Keep only the edges that satisfy the predicate. /O(n + e)/.

filterEdges :: (Edge n e -> Bool) -> Graph n e -> Graph n e
filterEdges f =
  Graph .
  Map.mapWithKey (\s ->
    Map.filterWithKey (\t l ->
      f (Edge { source = s, target = t, label = l }))) .
  graph

-- | Unzips the graph. /O(n + e)/.

-- This is a naive implementation that uses fmap.

unzip :: Graph n (e, e') -> (Graph n e, Graph n e')
unzip g = (fst <$> g, snd <$> g)

-- | @composeWith times plus g g'@ finds all edges
--   @s --c_i--> t_i --d_i--> u@ and constructs the
--   result graph from @edge(s,u) = sum_i (c_i times d_i)@.
--
--   Complexity:  For each edge @s --> t@ in @g@ we look up
--   all edges starting with @t@ in @g'@.
--
--   Precondition: The two graphs must have exactly the same nodes.

composeWith ::
  Ord n =>
  (c -> d -> e) -> (e -> e -> e) ->
  Graph n c -> Graph n d -> Graph n e
composeWith times plus (Graph g) (Graph g') = Graph (Map.map comp g)
  where
  comp m = Map.fromListWith plus
    [ (u, c `times` d)
    | (t, c) <- Map.assocs m
    , m'     <- maybeToList (Map.lookup t g')
    , (u, d) <- Map.assocs m'
    ]

------------------------------------------------------------------------
-- Strongly connected components

-- | The graph's strongly connected components, in reverse topological
-- order.

sccs' :: Ord n => Graph n e -> [Graph.SCC n]
sccs' g =
  Graph.stronglyConnComp
    [ (n, n, map target (edgesFrom g [n]))
    | n <- Set.toList (nodes g)
    ]

-- | The graph's strongly connected components, in reverse topological
-- order.

sccs :: Ord n => Graph n e -> [[n]]
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
  isAcyclic (Tree.Node r []) = r `notElem` (dagGraph g Array.! r)
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
  lookup' g k = fromMaybe __IMPOSSIBLE__ (IntMap.lookup k g)

  lookup'' g k = fromMaybe __IMPOSSIBLE__ (Map.lookup k g)

  reachable' n =
    concatMap (Graph.flattenSCC . lookup' (dagComponentMap g)) $
    Graph.reachable (dagGraph g) (lookup'' (dagNodeMap g) n)

-- | Constructs a DAG containing the graph's strongly connected
-- components.

sccDAG' ::
  forall n e. Ord n
  => Graph n e
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
      , let j = fromMaybe __IMPOSSIBLE__ (Map.lookup (target e) firstNodeMap)
      , j /= i
      ]

  (theDAG, _, toVertex) =
    Graph.graphFromEdges
      [ (i, i, targets i (Graph.flattenSCC c))
      | (i, c) <- components
      ]

  convertInt :: Int -> Graph.Vertex
  convertInt i = fromMaybe __IMPOSSIBLE__ (toVertex i)

  componentMap :: IntMap (Graph.SCC n)
  componentMap = IntMap.fromList (map (mapFst convertInt) components)

  secondNodeMap :: Map n Int
  secondNodeMap = Map.map convertInt firstNodeMap

-- | Constructs a DAG containing the graph's strongly connected
-- components.

sccDAG :: Ord n => Graph n e -> DAG n
sccDAG g = sccDAG' g (sccs' g)

------------------------------------------------------------------------
-- Reachability

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

reachableFrom :: Ord n => Graph n e -> n -> Map n (Int, [Edge n e])
reachableFrom g n = reachableFromInternal g (Set.singleton n)

-- | @reachableFromSet g ns@ is a set containing all nodes reachable
-- from @ns@ in @g@.
--
-- Precondition: Every node in @ns@ must be a node in @g@. The number
-- of nodes in the graph must not be larger than @'maxBound' ::
-- 'Int'@.
--
-- Amortised time complexity (assuming that comparisons take constant
-- time): /O((|@ns@| + e) log n)/.

reachableFromSet :: Ord n => Graph n e -> Set n -> Set n
reachableFromSet g ns = Map.keysSet (reachableFromInternal g ns)

-- | Used to implement 'reachableFrom' and 'reachableFromSet'.

reachableFromInternal ::
  Ord n => Graph n e -> Set n -> Map n (Int, [Edge n e])
reachableFromInternal g ns =
  bfs (SQ.fromList (map (, BQ.empty) (Set.toList ns))) Map.empty
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
-- predicates take constant time to compute): /O(n + e log n)/.

walkSatisfying ::
  Ord n =>
  (Edge n e -> Bool) -> (Edge n e -> Bool) ->
  Graph n e -> n -> n -> Maybe [Edge n e]
walkSatisfying every some g from to =
  case
    [ (l1 + l2, p1 ++ [e] ++ map transposeEdge (reverse p2))
    | e <- everyEdges
    , some e
    , (l1, p1) <- maybeToList (Map.lookup (source e) fromReaches)
    , (l2, p2) <- maybeToList (Map.lookup (target e) reachesTo)
    ] of
    []  -> Nothing
    ess -> Just $ snd $ List.minimumBy (compare `on` fst) ess
  where
  everyEdges = [ e | e <- edges g, every e ]

  fromReaches = reachableFrom (fromEdges everyEdges) from

  reachesTo =
    reachableFrom (fromEdges (map transposeEdge everyEdges)) to

------------------------------------------------------------------------
-- Transitive closure

-- | Transitive closure ported from "Agda.Termination.CallGraph".
--
--   Relatively efficient, see Issue 1560.

complete :: (Eq e, Null e, SemiRing e, Ord n) => Graph n e -> Graph n e
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

completeIter :: (Eq e, Null e, SemiRing e, Ord n) => Graph n e -> [(Graph n e, Graph n e)]
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
  Graph n e -> Graph n e
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
    fromEdges [ Edge (indexMap Map.! i) (indexMap Map.! j) e
              | ((i, j), e) <- Array.assocs m
              , e /= ozero
              ]
      `union`
    fromNodeSet (nodes g)

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
  Graph n e -> (Graph n e, [Graph.SCC n])
gaussJordanFloydWarshallMcNaughtonYamada g =
  (loop components g, components)
  where
  components = sccs' g
  forwardDAG = sccDAG' g components
  reverseDAG = oppositeDAG forwardDAG

  loop :: [Graph.SCC n] -> Graph n e -> Graph n e
  loop []           !g = g
  loop (scc : sccs)  g =
    loop sccs (foldr step g (Graph.flattenSCC scc))
    where
    -- All nodes that are reachable from the SCC.
    canBeReached = reachable forwardDAG scc
    -- All nodes that can reach the SCC.
    canReach     = reachable reverseDAG scc

    step :: n -> Graph n e -> Graph n e
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

      lookup' s t = fromMaybe ozero (lookup s t g)
