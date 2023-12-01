{-# LANGUAGE TemplateHaskell #-}

-- | Properties for graph library.

module Internal.Utils.Graph.AdjacencyMap.Unidirectional ( tests ) where

import Agda.TypeChecking.Positivity.Occurrence

import Agda.Utils.Function (iterateUntil)
import Agda.Utils.Functor
import Agda.Utils.Graph.AdjacencyMap.Unidirectional as Graph
import Agda.Utils.List (distinct, headWithDefault, nubOn)
import Agda.Utils.Null as Null
import Agda.Utils.SemiRing
import Agda.Utils.Singleton (Singleton)
import qualified Agda.Utils.Singleton as Singleton
import Agda.Utils.Impossible
import Agda.Syntax.Common.Pretty

import Control.Monad

import qualified Data.Foldable as Fold
import Data.Function (on)
import qualified Data.Graph as Graph
import qualified Data.List as List
import Data.Maybe
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set

import Internal.Helpers
import Internal.TypeChecking.Positivity.Occurrence ()

import Prelude hiding (null)

import Test.QuickCheck as QuickCheck


------------------------------------------------------------------------
-- * Generators
------------------------------------------------------------------------

instance (Arbitrary n, Arbitrary e) => Arbitrary (Edge n e) where
  arbitrary = Edge <$> arbitrary <*> arbitrary <*> arbitrary

instance (CoArbitrary n, CoArbitrary e) => CoArbitrary (Edge n e) where
  coarbitrary (Edge s t e) = coarbitrary s . coarbitrary t . coarbitrary e

instance (Ord n, Arbitrary n, Arbitrary e) =>
         Arbitrary (Graph n e) where
  arbitrary = do
    nodes <- sized $ \ n -> resize (2 * isqrt n) arbitrary
    edges <- edgesWithNodesFrom nodes
    let g1 = fromEdges edges
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

-- | Generates a list of edges with nodes from the given list.

edgesWithNodesFrom :: Arbitrary e => [n] -> Gen [Edge n e]
edgesWithNodesFrom nodes =
  mapM (\(n1, n2) -> Edge n1 n2 <$> arbitrary) =<<
  listOfElements ((,) <$> nodes <*> nodes)

prop_edgesWithNodesFrom :: [N] -> Property
prop_edgesWithNodesFrom ns =
  forAll (edgesWithNodesFrom ns :: Gen [Edge N E]) $ \es ->
    all inList es
  where
  nsSet               = Set.fromList ns
  inList (Edge s t _) = all (flip Set.member nsSet) [s, t]

-- | Generates a graph with exactly the given nodes.

graphWithNodes :: (Ord n, Arbitrary e) => [n] -> Gen (Graph n e)
graphWithNodes nodes = do
  edges <- edgesWithNodesFrom nodes
  return (fromEdges edges `union` fromNodes nodes)

prop_graphWithNodes :: [N] -> Property
prop_graphWithNodes ns =
  forAll (graphWithNodes ns :: Gen G) $ \g ->
    nodes g == Set.fromList ns

-- | Generates an acyclic graph.

acyclicGraph ::
  forall n e. (Ord n, Arbitrary n, Arbitrary e) => Gen (Graph n e)
acyclicGraph = do
  nodes      <- nubOn id <$> arbitrary
  (_, edges) <- foldM (flip addEdgesFrom) (Set.empty, []) nodes
  return (fromEdges edges `union` fromNodes nodes)
  where
  addEdgesFrom :: n -> (Set n, [Edge n e]) -> Gen (Set n, [Edge n e])
  addEdgesFrom n (seen, es) =
    (Set.insert n seen,) <$>
    if null seen
    then return es
    else (++ es) <$> listOf edge
    where
    edge = do
      n' <- elements (Set.toList seen)
      e  <- arbitrary
      return (Edge { source = n, target = n', label = e })

prop_acyclicGraph :: Property
prop_acyclicGraph =
  forAll (acyclicGraph :: Gen G) acyclic

-- | Generates a node from the graph. (Unless the graph is empty.)

nodeIn :: (Ord n, Arbitrary n) => Graph n e -> Gen n
nodeIn g = elementsUnlessEmpty (Set.toList $ nodes g)

-- | Generates an edge from the graph. (Unless the graph contains no
-- edges.)

edgeIn :: (Arbitrary n, Arbitrary e) =>
          Graph n e -> Gen (Edge n e)
edgeIn g = elementsUnlessEmpty (edges g)

------------------------------------------------------------------------
-- * Helper code
------------------------------------------------------------------------

-- | Sample graph type used to test some graph algorithms.

type G = Graph N E

-- | Sample edge type used to test some graph algorithms.

type E = Occurrence

-- | Sample node type used to test some graph algorithms.

newtype N = N (Positive Int)
  deriving (Arbitrary, Eq, Ord)

n :: Int -> N
n = N . Positive

instance Show N where
  show (N (Positive n)) = "n " ++ show n

instance Pretty N where
  pretty = text . show

instance CoArbitrary N where
  coarbitrary (N (Positive n)) = coarbitrary n

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

connectivityGraph :: Ord n => Graph n e -> Graph n Connected
connectivityGraph =
  fst . gaussJordanFloydWarshallMcNaughtonYamada .
  fmap (const oone)

connected :: Ord n => Graph n Connected -> n -> n -> Bool
connected g i j = Graph.lookup i j g == Just Connected

-- | A graph with nodes from @1@ to the given number that contains an
-- edge from @m@ to @n@ if and only if @m > n@.
--
-- Precondition: The number must be positive.

decreasingGraph :: Int -> Graph Int ()
decreasingGraph n
  | n == 1    = fromNodes [1]
  | otherwise = foldr (\n' -> insert n n' ()) g [1 .. n-1]
    where
    g = decreasingGraph (n - 1)

------------------------------------------------------------------------
-- * The graph invariant is established/preserved by all operations
------------------------------------------------------------------------

prop_invariant :: G -> Bool
prop_invariant = invariant

prop_invariant_shrink :: G -> Bool
prop_invariant_shrink = all invariant . shrink

prop_invariant_acyclicGraph :: Property
prop_invariant_acyclicGraph =
  forAll (acyclicGraph :: Gen G) invariant

prop_invariant_fromNodes :: [N] -> Bool
prop_invariant_fromNodes = invariant . fromNodes

prop_invariant_fromNodeSet :: Set.Set N -> Bool
prop_invariant_fromNodeSet = invariant . fromNodeSet

prop_invariant_fromEdges :: [Edge N E] -> Bool
prop_invariant_fromEdges = invariant . fromEdges

prop_invariant_fromEdgesWith :: (E -> E -> E) -> [Edge N E] -> Bool
prop_invariant_fromEdgesWith f = invariant . fromEdgesWith f

prop_invariant_empty :: Bool
prop_invariant_empty = invariant (Graph.empty :: G)

prop_invariant_singleton :: N -> N -> E -> Bool
prop_invariant_singleton s t e = invariant (singleton s t e)

prop_invariant_insert :: N -> N -> E -> G -> Bool
prop_invariant_insert s t e = invariant . insert s t e

prop_invariant_insertEdge :: Edge N E -> G -> Bool
prop_invariant_insertEdge e = invariant . insertEdge e

prop_invariant_insertWith :: (E -> E -> E) -> N -> N -> E -> G -> Bool
prop_invariant_insertWith f s t e = invariant . insertWith f s t e

prop_invariant_insertEdgeWith ::
  (E -> E -> E) -> Edge N E -> G -> Bool
prop_invariant_insertEdgeWith f e = invariant . insertEdgeWith f e

prop_invariant_union :: G -> G -> Bool
prop_invariant_union g1 g2 = invariant (union g1 g2)

prop_invariant_unionWith :: (E -> E -> E) -> G -> G -> Bool
prop_invariant_unionWith f g1 g2 = invariant (unionWith f g1 g2)

prop_invariant_unions :: [G] -> Bool
prop_invariant_unions = invariant . unions

prop_invariant_unionsWith :: (E -> E -> E) -> [G] -> Bool
prop_invariant_unionsWith f = invariant . unionsWith f

prop_invariant_mapWithEdge :: (Edge N E -> E) -> G -> Bool
prop_invariant_mapWithEdge f= invariant . mapWithEdge f

prop_invariant_transpose :: G -> Bool
prop_invariant_transpose = invariant . transpose

prop_invariant_clean :: G -> Bool
prop_invariant_clean = invariant . clean

prop_invariant_filterNodes :: (N -> Bool) -> G -> Bool
prop_invariant_filterNodes p g =
  invariant (filterNodes p g)

prop_invariant_removeNodes :: G -> Property
prop_invariant_removeNodes g =
  forAll (listOf (frequency [(5, nodeIn g), (1, arbitrary)])) $ \ns ->
    invariant (removeNodes (Set.fromList ns) g)

prop_invariant_removeNode :: G -> Property
prop_invariant_removeNode g =
  forAll (frequency [(5, nodeIn g), (1, arbitrary)]) $ \n ->
    invariant (removeNode n g)

prop_invariant_removeEdge :: G -> Property
prop_invariant_removeEdge g =
  forAll (vectorOf 2 (frequency [ (3, nodeIn g)
                                , (1, arbitrary)
                                ])) $ \[m, n] ->
    invariant (removeEdge m n g)

prop_invariant_filterEdges :: (Edge N E -> Bool) -> G -> Bool
prop_invariant_filterEdges f = invariant . filterEdges f

prop_invariant_filterNodesKeepingEdges :: (N -> Bool) -> Property
prop_invariant_filterNodesKeepingEdges p =
  forAll (acyclicGraph :: Gen G) $ \g ->
  invariant (filterNodesKeepingEdges p g)

prop_invariant_renameNodes :: G -> Bool
prop_invariant_renameNodes = invariant . renameNodes ren
  where
  ren (N (Positive n)) = - n

prop_invariant_renameNodesMonotonic :: G -> Bool
prop_invariant_renameNodesMonotonic =
  invariant . renameNodesMonotonic ren
  where
  ren (N (Positive n)) = n

prop_invariant_addUniqueInts :: G -> Bool
prop_invariant_addUniqueInts = invariant . addUniqueInts

prop_invariant_unzip :: G -> Bool
prop_invariant_unzip g = invariant g1 && invariant g2
  where
  (g1, g2) = Graph.unzip (fmap (\e -> (e, e)) g)

prop_invariant_composeWith ::
  (E -> E -> E) -> (E -> E -> E) -> G -> Property
prop_invariant_composeWith f1 f2 g1 =
  forAll (graphWithNodes (Set.toList (nodes g1))) $ \g2 ->
    invariant (composeWith f1 f2 g1 g2)

prop_invariant_longestPaths :: Property
prop_invariant_longestPaths =
  forAll (acyclicGraph :: Gen G) $ \g ->
    invariant (longestPaths g)

prop_invariant_complete :: G -> Bool
prop_invariant_complete = invariant . complete

prop_invariant_completeIter :: G -> Bool
prop_invariant_completeIter g =
  all (\(g1, g2) -> invariant g1 && invariant g2) (completeIter g)

prop_invariant_gaussEtAlReference ::
  G -> Bool
prop_invariant_gaussEtAlReference =
  invariant . gaussJordanFloydWarshallMcNaughtonYamadaReference

prop_invariant_gaussEtAl :: G -> Bool
prop_invariant_gaussEtAl =
  invariant . fst . gaussJordanFloydWarshallMcNaughtonYamada

prop_invariant_transitiveReduction :: Property
prop_invariant_transitiveReduction =
  forAll (acyclicGraph :: Gen G) $ \g ->
    invariant (transitiveReduction g)

------------------------------------------------------------------------
-- * Graph properties
------------------------------------------------------------------------

-- The output of show is correct.

prop_show :: G -> Bool
prop_show g =
  g == union (fromEdges (edges g))
             (fromNodes (Set.toList (isolatedNodes g)))

prop_neighbours :: N -> G -> Bool
prop_neighbours s g =
  neighbours s g == map (\ (Edge s t e) -> (t, e)) (edgesFrom g [s])

prop_edgesFrom :: G -> Property
prop_edgesFrom g =
  forAll (listOf (frequency [(5, nodeIn g), (1, arbitrary)])) $ \ns' ->
    let ns = List.nub ns'
        es = edgesFrom g ns
    in
    -- No duplicates.
    List.sort es == List.nub (List.sort es)

prop_edgesTo :: G -> Property
prop_edgesTo g =
  forAll (listOf (frequency [(5, nodeIn g), (1, arbitrary)])) $ \ns' ->
    let ns = List.nub ns'
        es = edgesTo g ns
    in
    -- No duplicates.
    List.sort es == List.nub (List.sort es)

prop_nodes_fromNodes :: [N] -> Bool
prop_nodes_fromNodes ns = nodes (fromNodes ns) == Set.fromList ns

prop_nodes_sourceNodes_targetNodes_isolatedNodes :: G -> Bool
prop_nodes_sourceNodes_targetNodes_isolatedNodes g =
  nodes g == Set.unions [ sourceNodes g
                        , targetNodes g
                        , isolatedNodes g
                        ]
    &&
  all (\n -> not $ null (neighbours n g)) (Set.toList (sourceNodes g))
    &&
  all (\n -> not $ null (edgesTo g [n])) (Set.toList (targetNodes g))
    &&
  all (\n -> null (neighbours n g) && null (edgesTo g [n]))
      (Set.toList (isolatedNodes g))

prop_computeNodes :: G -> Bool
prop_computeNodes g =
  srcNodes ns == sourceNodes g
    &&
  tgtNodes ns == targetNodes g
    &&
  allNodes ns == nodes g
  where
  ns = computeNodes g

prop_insert :: N -> N -> E -> G -> Bool
prop_insert s t e g = insert s t e g == union (singleton s t e) g

prop_insertWith :: (E -> E -> E) -> N -> N -> E -> G -> Bool
prop_insertWith f s t e g =
  insertWith f s t e g == unionWith (flip f) g (singleton s t e)

prop_transpose :: G -> Bool
prop_transpose g = transpose (transpose g) == g

prop_clean :: G -> Bool
prop_clean g =
  all (not . null . Graph.label) (edges (clean g))
    &&
  discrete g == (null . edges . clean) g

prop_filterNodes :: (N -> Bool) -> G -> Bool
prop_filterNodes p g =
  Set.filter p (nodes g) == nodes (filterNodes p g)

prop_removeEdge :: G -> Property
prop_removeEdge g =
  (not (null (edges g)) ==>
   forAll (edgeIn g) $ \e ->
     insertEdge e (removeEdge (source e) (target e) g) == g)
    .&&.
  (not (null (nodes g)) ==>
   forAll (vectorOf 2 (nodeIn g)) $ \[s, t] ->
   not (t `elem` map target (edgesFrom g [s])) ==>
   forAll arbitrary $ \l ->
     removeEdge s t (insertEdge (Edge s t l) g) == g)

prop_filterNodesKeepingEdges :: (N -> Bool) -> Property
prop_filterNodesKeepingEdges p =
  forAll (acyclicGraph :: Gen G) $ \g ->
  not (null (nodes g)) ==>
  let g' = filterNodesKeepingEdges p g in
  forAll (nodeIn g) $ \n ->
    if p n
    then Set.filter p (Map.keysSet (reachableFrom g n)) ==
         Map.keysSet (reachableFrom g' n)
    else not (n `Set.member` nodes g')

prop_renameNodes :: G -> Bool
prop_renameNodes g =
  renameNodes inv (renameNodes ren g) == g
  where
  ren (N (Positive n)) = - n
  inv n                = N (Positive (- n))

prop_renameNodesMonotonic :: G -> Bool
prop_renameNodesMonotonic g =
  renameNodesMonotonic inv (renameNodesMonotonic ren g) == g
  where
  ren (N (Positive n)) = n
  inv n                = N (Positive n)

prop_addUniqueInts :: G -> Bool
prop_addUniqueInts g =
  renameNodes otherValue (addUniqueInts g) == g

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
      headWithDefault __IMPOSSIBLE__
        [ i
        | (i, ns) <- zip [1..] (reverse components)
        , k `elem` ns
        ]

prop_oppositeDAG :: G -> Bool
prop_oppositeDAG g =
  dagInvariant (oppositeDAG (sccDAG g))

prop_sccDAG :: G -> Bool
prop_sccDAG g =
  dagInvariant dag
    &&
  nodes g == Map.keysSet (dagNodeMap dag)
  where
  dag = sccDAG g

-- | @isWalk g from to es@ is 'True' iff @es@ is a walk from @from@ to
-- @to@ in @g@.

isWalk :: G -> N -> N -> [Edge N E] -> Bool
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

prop_reachableFromSet :: G -> Property
prop_reachableFromSet g =
  not (Set.null (nodes g)) ==>
  forAll (listOf (nodeIn g)) $ \ us' ->
    let us              = Set.fromList us'
        reachableFromUs = reachableFromSet g us in
    -- A path is found from us to v iff v is in us or there is a
    -- non-empty path from us to v (according to 'connectivityGraph'
    -- and 'connected').
    Fold.all (\v -> Set.member v reachableFromUs
                      ==
                    (Set.member v us ||
                     any (\u -> connected cg u v) (Set.toList us)))
             (nodes g)
  where
  cg = connectivityGraph g

prop_walkSatisfying ::
  G -> (Edge N E -> Bool) -> (Edge N E -> Bool) -> Property
prop_walkSatisfying g every some =
  forAll (nodeIn g) $ \from ->
  forAll (nodeIn g) $ \to ->
    case walkSatisfying every some g from to of
      Nothing -> QuickCheck.label "no walk" True
      Just es -> QuickCheck.label (show (length es) ++ " steps") $
                   isWalk g from to es
                     &&
                   all every es && any some es

prop_longestPaths1 :: Property
prop_longestPaths1 =
  forAll (acyclicGraph :: Gen G) $ \g ->
  not (null (nodes g)) ==>
  let g' = longestPaths g in
  property
    (all (\(n, ps) -> all ((== n) . length) ps) $
     map Graph.label (edges g'))
    .&&.
  (forAll (nodeIn g) $ \n ->
   Map.keysSet (reachableFrom g n)
     ==
   Map.keysSet (neighboursMap n g'))

prop_longestPaths2 :: Property
prop_longestPaths2 =
  forAll positive $ \n ->
  let g = decreasingGraph n in
  forAll (nodeIn g) $ \m ->
  forAll (nodeIn g) $ \n ->
  let e = Map.lookup n (neighboursMap m (longestPaths g)) in
  counterexample (show e) $
  if m < n
  then e == Nothing
  else fmap fst e == Just (m - n)

-- | Computes the transitive closure of the graph.
--
-- Note that this algorithm is not guaranteed to be correct (or
-- terminate) for arbitrary semirings.
--
-- This function operates on the entire graph at once.

transitiveClosure1 :: (Eq e, SemiRing e, Ord n) =>
                      Graph n e -> Graph n e
transitiveClosure1 = completeUntilWith (==) otimes oplus

-- | Computes the transitive closure of the graph.
--
-- Note that this algorithm is not guaranteed to be correct (or
-- terminate) for arbitrary semirings.
--
-- This function operates on the entire graph at once.

completeUntilWith ::
  (Ord n) =>
  (Graph n e -> Graph n e -> Bool) ->
  (e -> e -> e) -> (e -> e -> e) -> Graph n e -> Graph n e
completeUntilWith done otimes oplus = iterateUntil done growGraph
  where
  -- @growGraph g@ unions @g@ with @(s --> t) `compose` g@ for each
  -- edge @s --> t@ in @g@
  growGraph g =
    List.foldl' (unionWith oplus) g $ for (edges g) $ \ (Edge s t e) ->
    case Map.lookup t (graph g) of
      Just es -> Graph $ Map.singleton s $ Map.map (otimes e) es
      Nothing -> Graph.empty

-- | Equality modulo empty edges.

(~~) :: (Eq e, Ord n, Null e) => Graph n e -> Graph n e -> Bool
(~~) = (==) `on` clean

prop_complete :: G -> Bool
prop_complete g =
  complete g ~~ transitiveClosure1 g

prop_gaussEtAlReference :: G -> Bool
prop_gaussEtAlReference g =
  gaussJordanFloydWarshallMcNaughtonYamadaReference g ~~
  transitiveClosure1 g

prop_gaussEtAl :: G -> Property
prop_gaussEtAl g =
  QuickCheck.label sccInfo $
    fst (gaussJordanFloydWarshallMcNaughtonYamada g) ~~
    gaussJordanFloydWarshallMcNaughtonYamadaReference g
  where
  sccInfo =
    (if noSCCs <= 3 then "   " ++ show noSCCs
                    else ">= 4") ++
    " strongly connected component(s)"
    where noSCCs = length (sccs g)

prop_transitiveReduction1 :: Property
prop_transitiveReduction1 =
  forAll (acyclicGraph :: Gen G) $ \g ->
  fmap (const ())
    (transitiveClosure (fmap Just (transitiveReduction g)))
    ==
  fmap (const ()) (transitiveClosure (fmap Just g))

prop_transitiveReduction2 :: Property
prop_transitiveReduction2 =
  forAll positive $ \n ->
  let g = decreasingGraph n in
  Set.fromList (edges (transitiveReduction g)) ==
  Set.fromList
    [ Edge { source = 1 + i, target = i, label = () }
    | i <- [1 .. n - 1]
    ]

-- | A property for
-- 'Agda.TypeChecking.Positivity.Occurrence.productOfEdgesInBoundedWalk'.

prop_productOfEdgesInBoundedWalk :: G -> Property
prop_productOfEdgesInBoundedWalk g =
  forAll (nodeIn g) $ \u ->
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

------------------------------------------------------------------------
-- * All tests
------------------------------------------------------------------------

-- Template Haskell hack to make the following $allProperties work
-- under ghc-7.8.
return [] -- KEEP!

-- | All tests as collected by 'allProperties'.
--
-- Using 'allProperties' is convenient and superior to the manual
-- enumeration of tests, since the name of the property is added
-- automatically.

tests :: TestTree
tests = testProperties "Internal.Utils.Graph.AdjacencyMap.Unidirectional" $allProperties

-- Abbreviations for testing in interpreter.

g1, g2, g3, g4 :: Graph N E
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
