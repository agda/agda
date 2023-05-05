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
  , filterNodes
  , filterEdges
  , filterNodesKeepingEdges
  , renameNodes, renameNodesMonotonic
  , WithUniqueInt(..), addUniqueInts
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
  , longestPaths
    -- * Transitive closure
  , gaussJordanFloydWarshallMcNaughtonYamada
  , gaussJordanFloydWarshallMcNaughtonYamadaReference
  , transitiveClosure
  , transitiveReduction
  , complete, completeIter
  )
  where

import Prelude hiding ( lookup, null, unzip )




import qualified Data.Array.IArray as Array
import Data.Sequence (Seq)
import qualified Data.Sequence as Seq
import Data.Function (on)
import qualified Data.Graph as Graph
import Data.IntMap.Strict (IntMap)
import qualified Data.IntMap.Strict as IntMap
import qualified Data.IntSet as IntSet
import qualified Data.List as List
import qualified Data.Map.Strict as Map
import Data.Map.Strict (Map)
import Data.Foldable (toList)

import Data.Maybe (maybeToList, fromMaybe)
import qualified Data.Set as Set
import Data.Set (Set)
import qualified Data.Tree as Tree

import Agda.Utils.Function

import Agda.Utils.Null (Null(null))
import qualified Agda.Utils.Null as Null
import Agda.Utils.Pretty
import Agda.Utils.SemiRing
import Agda.Utils.Tuple

import Agda.Utils.Impossible
import Agda.Utils.Functor

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
-- Time complexity: /O(n₁ log (n₂/n₁ + 1) + e₁ log e₂)/, where /n₁/ is
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

-- | The graph @filterNodes p g@ contains exactly those nodes from @g@
-- that satisfy the predicate @p@. Edges to or from nodes that are
-- removed are also removed. /O(n + e)/.

filterNodes :: Ord n => (n -> Bool) -> Graph n e -> Graph n e
filterNodes p (Graph g) = Graph (Map.mapMaybeWithKey remSrc g)
  where
  remSrc s m
    | p s       = Just (Map.filterWithKey (\t _ -> p t) m)
    | otherwise = Nothing

-- | @removeNodes ns g@ removes the nodes in @ns@ (and all
-- corresponding edges) from @g@. /O((n + e) log |@ns@|)/.

removeNodes :: Ord n => Set n -> Graph n e -> Graph n e
removeNodes ns = filterNodes (\n -> not (Set.member n ns))

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

-- | Removes the nodes that do not satisfy the predicate from the
-- graph, but keeps the edges: if there is a path in the original
-- graph between two nodes that are retained, then there is a path
-- between these two nodes also in the resulting graph.
--
-- Precondition: The graph must be acyclic.
--
-- Worst-case time complexity: /O(e n log n)/ (this has not been
-- verified carefully).

filterNodesKeepingEdges ::
  forall n e. (Ord n, SemiRing e) =>
  (n -> Bool) -> Graph n e -> Graph n e
filterNodesKeepingEdges p g =
  foldr (insertEdgeWith oplus) (filterNodes p g)
    (fst edgesToAddAndRemove)
  where
  -- The new edges that should be added, and a map from nodes that
  -- should be removed to edges that should potentially be added
  -- (after being combined with paths into the nodes that should be
  -- removed).
  edgesToAddAndRemove :: ([Edge n e], Map n (Map n e))
  edgesToAddAndRemove =
    List.foldl' edgesToAddAndRemoveForSCC ([], Map.empty) (sccs' g)

  edgesToAddAndRemoveForSCC (add, !remove) (Graph.AcyclicSCC n)
    | p n =
      ( (do (n', e) <- neighbours n g
            case Map.lookup n' remove of
              Nothing -> []
              Just es ->
                for (Map.toList es) $ \(n', e') -> Edge
                  { source = n
                  , target = n'
                  , label  = e `otimes` e'
                  })
          ++
        add
      , remove
      )
    | otherwise =
      ( add
      , Map.insert
          n
          (Map.unionsWith oplus $
           for (neighbours n g) $ \(n', e) ->
             case Map.lookup n' remove of
               Nothing -> Map.singleton n' e
               Just es -> fmap (e `otimes`) es)
          remove
      )
  edgesToAddAndRemoveForSCC _ (Graph.CyclicSCC{}) = __IMPOSSIBLE__

-- | Renames the nodes.
--
-- Precondition: The renaming function must be injective.
--
-- Time complexity: /O((n + e) log n)/.

renameNodes :: Ord n2 => (n1 -> n2) -> Graph n1 e -> Graph n2 e
renameNodes ren =
  Graph .
  fmap (Map.mapKeys ren) .
  Map.mapKeys ren .
  graph

-- | Renames the nodes.
--
-- Precondition: The renaming function @ren@ must be strictly
-- increasing (if @x '<' y@ then @ren x '<' ren y@).
--
-- Time complexity: /O(n + e)/.

renameNodesMonotonic ::
  (Ord n1, Ord n2) => (n1 -> n2) -> Graph n1 e -> Graph n2 e
renameNodesMonotonic ren =
  Graph .
  fmap (Map.mapKeysMonotonic ren) .
  Map.mapKeysMonotonic ren .
  graph

-- | @WithUniqueInt n@ consists of pairs of (unique) 'Int's and values
-- of type @n@.
--
-- Values of this type are compared by comparing the 'Int's.

data WithUniqueInt n = WithUniqueInt
  { uniqueInt  :: !Int
  , otherValue :: !n
  }
  deriving (Show, Functor)

instance Eq (WithUniqueInt n) where
  WithUniqueInt i1 _ == WithUniqueInt i2 _ = i1 == i2

instance Ord (WithUniqueInt n) where
  compare (WithUniqueInt i1 _) (WithUniqueInt i2 _) = compare i1 i2

instance Pretty n => Pretty (WithUniqueInt n) where
  pretty (WithUniqueInt i n) =
    parens ((pretty i <> comma) <+> pretty n)

-- | Combines each node label with a unique 'Int'.
--
-- Precondition: The number of nodes in the graph must not be larger
-- than @'maxBound' :: 'Int'@.
--
-- Time complexity: /O(n + e log n)/.

addUniqueInts ::
  forall n e. Ord n => Graph n e -> Graph (WithUniqueInt n) e
addUniqueInts g =
  Graph $
  Map.fromDistinctAscList $
  map (\(i, (n, m)) ->
        (WithUniqueInt i n, Map.mapKeysMonotonic ren m)) $
  zip [0..] $
  Map.toAscList $
  graph g
  where
  renaming :: Map n Int
  renaming = snd $ Map.mapAccum (\i _ -> (succ i, i)) 0 (graph g)

  ren :: n -> WithUniqueInt n
  ren n = case Map.lookup n renaming of
    Just i  -> WithUniqueInt i n
    Nothing -> __IMPOSSIBLE__

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
--
-- The time complexity is likely /O(n + e log n)/ (but this depends on
-- the, at the time of writing undocumented, time complexity of
-- 'Graph.stronglyConnComp').

sccs' :: Ord n => Graph n e -> [Graph.SCC n]
sccs' g =
  Graph.stronglyConnComp
    [ (n, n, Map.keys es)
    | (n, es) <- Map.toAscList (graph g)
    ]
    -- Graph.stronglyConnComp sorts this list, and the sorting
    -- algorithm that is used is adaptive, so it may make sense to
    -- generate a sorted list. (These comments apply to one specific
    -- version of the code in Graph, compiled in a specific way.)

-- | The graph's strongly connected components, in reverse topological
-- order.
--
-- The time complexity is likely /O(n + e log n)/ (but this depends on
-- the, at the time of writing undocumented, time complexity of
-- 'Graph.stronglyConnComp').

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
  bfs (Seq.fromList (map (, Seq.empty) (toList ns))) Map.empty
  where
  bfs !q !map = case Seq.viewl q of
    Seq.EmptyL -> map
    (u, p) Seq.:< q ->
      if u `Map.member` map
      then bfs q map
      else bfs (foldr (flip (Seq.|>)) q
                      [ (v, p Seq.|> Edge u v e)
                      | (v, e) <- neighbours u g
                      ])
               (let n = Seq.length p in
                n `seq` Map.insert u (n, toList p) map)

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

-- | Constructs a graph @g'@ with the same nodes as the original graph
-- @g@. In @g'@ there is an edge from @n1@ to @n2@ if and only if
-- there is a (possibly empty) simple path from @n1@ to @n2@ in @g@.
-- In that case the edge is labelled with all of the longest (in terms
-- of numbers of edges) simple paths from @n1@ to @n2@ in @g@, as well
-- as the lengths of these paths.
--
-- Precondition: The graph must be acyclic. The number of nodes in the
-- graph must not be larger than @'maxBound' :: 'Int'@.
--
-- Worst-case time complexity (if the paths are not inspected):
-- /O(e n log n)/ (this has not been verified carefully).
--
-- The algorithm is based on one found on Wikipedia.

longestPaths ::
  forall n e. Ord n => Graph n e -> Graph n (Int, [[Edge n e]])
longestPaths g =
  Graph $
  fmap (fmap (mapSnd toList)) $
  List.foldl' (flip addLongestFrom) Map.empty $
  sccs' g
  where
  addLongestFrom ::
    Graph.SCC n ->
    Map n (Map n (Int, Seq [Edge n e])) ->
    Map n (Map n (Int, Seq [Edge n e]))
  addLongestFrom Graph.CyclicSCC{}    !_  = __IMPOSSIBLE__
  addLongestFrom (Graph.AcyclicSCC n) pss =
    Map.insert n
      (Map.insert n (0, Seq.singleton []) $
       Map.unionsWith longest candidates)
      pss
    where
    longest p1@(n1, ps1) p2@(n2, ps2) = case compare n1 n2 of
      GT -> p1
      LT -> p2
      EQ -> (n1, ps1 Seq.>< ps2)

    candidates :: [Map n (Int, Seq [Edge n e])]
    candidates =
      for (neighbours n g) $ \(n', e) ->
      let edge = Edge
            { source = n
            , target = n'
            , label  = e
            }
      in case Map.lookup n' pss of
        Nothing -> Map.empty
        Just ps -> fmap (succ -*- fmap (edge :)) ps

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

-- | The transitive closure. Using 'gaussJordanFloydWarshallMcNaughtonYamada'.
--   NOTE: DO NOT USE () AS EDGE LABEL SINCE THIS MEANS EVERY EDGE IS CONSIDERED A ZERO EDGE AND NO
--         NEW EDGES WILL BE ADDED! Use 'Maybe ()' instead.
transitiveClosure :: (Ord n, Eq e, StarSemiRing e) => Graph n e -> Graph n e
transitiveClosure = fst . gaussJordanFloydWarshallMcNaughtonYamada

-- | The transitive reduction of the graph: a graph with the same
-- reachability relation as the graph, but with as few edges as
-- possible.
--
-- Precondition: The graph must be acyclic. The number of nodes in the
-- graph must not be larger than @'maxBound' :: 'Int'@.
--
-- Worst-case time complexity: /O(e n log n)/ (this has not been
-- verified carefully).
--
-- The algorithm is based on one found on Wikipedia.

transitiveReduction :: Ord n => Graph n e -> Graph n ()
transitiveReduction g =
  fmap (const ()) $
  filterEdges ((== 1) . fst . label) $
  longestPaths g
