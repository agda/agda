{- | Contains the algorithm for processing graph dependencies.

     The central structure of the algorithm is a bounded meet-semilattice of rigid size variables, where the upper bound is an infinite ordinal.
     In this file, the elements of the semilattice are referred to as size expressions.

     Given the semilattice, the algorithm tries to find an assignment of size expressions to all flexible variables.
     The main requirement is that the assignment should satisfy the _constraint graph_.
     The semantical meaning of the constraint graph is that it completely describes the dependencies between flexible variables in
     some internal term.

     There is a trivial solution which assigns the inifnity to all flexible variables.
     However, it is preferable to find a more precise assignment. In ideal case, we need to find a "universal" one,
     i.e. an assignment, such that for any other assignment all variables are assigned to a bigger or equal size expression.
     The semantical meaning here is that we are trying to find a witness of termination of a function,
     and the universal solution allows to get the most optimistic description of size dependencies for recursive calls.

     The algorithm here relies on the notion of clusters, which is explained in 'Agda.Termination.TypeBased.Patterns'
-}
module Agda.Termination.TypeBased.Graph where

import Agda.Termination.TypeBased.Monad
import Agda.Termination.TypeBased.Syntax
import Data.IntSet (IntSet)
import qualified Data.IntSet as IntSet
import qualified Data.List as List
import Data.IntMap (IntMap)
import qualified Data.IntMap as IntMap
import Control.Monad.Trans.State
import Agda.TypeChecking.Monad.Base
import qualified Agda.Termination.Order as Order
import Agda.Termination.Order (Order)
import Data.Maybe
import Agda.Utils.Impossible
import Debug.Trace
import Agda.TypeChecking.Monad.Signature
import Control.Monad
import Agda.TypeChecking.Monad.Debug
import Agda.TypeChecking.Pretty
import qualified Data.Graph as Graph
import qualified Agda.Syntax.Common.Pretty as P
import qualified Agda.Benchmarking as Benchmark
import qualified Agda.Utils.Graph.AdjacencyMap.Unidirectional as DGraph
import Agda.TypeChecking.Monad.Benchmark (billTo)
import Data.Either
import qualified Data.List.NonEmpty as NonEmpty
import Data.List.NonEmpty (NonEmpty(..), (<|))

-- A size expression is represented as a minimum of a set of rigid size variables,
-- where the length of the set is equal to the number of clusters.
-- This datatype represents an element of the bounded meet-semilattice mentioned above.
newtype SizeExpression = SEMeet [Int]
  deriving Eq

instance P.Pretty SizeExpression where
  pretty (SEMeet list) = case filter (/= (-1)) list of
    [] -> "∞"
    nonempty -> P.hcat $ P.punctuate " ∧ " (map (\i -> P.pretty (SDefined i)) nonempty)

type GraphEnv a = StateT SizeCheckerState TCM a

-- | 'simplifySizeGraph context graph' assigns all variables occurring in the graph to the variables from the context
-- The outline:
-- 1. Find all strongly connected components.
-- 2. Sort the obtained acyclic graph topologically.
-- 3. For each component in the order, assign the least upper bound of all its known lower bounds. If there are no lower bounds, apply a heuristic.
simplifySizeGraph :: [(Int, SizeBound)] -> [SConstraint] -> MonadSizeChecker (IntMap SizeExpression, IntMap Int)
simplifySizeGraph rigidContext graph = billTo [Benchmark.TypeBasedTermination, Benchmark.SizeGraphSolving] $ do
  let enrichedGraph = mapMaybe (\(i, b) -> case b of
        SizeBounded j -> Just (SConstraint SLte i j)
        SizeUnbounded -> Nothing) rigidContext ++ graph
  -- !! NOTE: The graph is reversed, since it is more performant to access its edges this way
  let adjacencyMap = DGraph.fromEdges (map (\(SConstraint rel from to) -> DGraph.Edge to from rel) enrichedGraph)

  let sccs = DGraph.sccs adjacencyMap

  currentRoot <- currentCheckedName
  -- The arity corresponds to the number of clusters
  arity <- getArity currentRoot
  undefinedVars <- getUndefinedSizes
  let baseSize = replicate arity (-1)
  bottomVars <- MSC $ gets scsBottomFlexVars
  contra <- getContravariantSizeVariables

  -- Lazy map representing an approximate cluster of each variable
  let rigidClusters = (mapMaybe (\(i, b) -> (i,) <$> findCluster rigidContext i) rigidContext)
  let rememberNeighbor v1 v2 = IntMap.insertWith (\n old -> NonEmpty.head n NonEmpty.<| old) v1 (NonEmpty.singleton v2)
  let neighbourMap = foldr (\(SConstraint _ from to) -> rememberNeighbor to from . rememberNeighbor from to) IntMap.empty enrichedGraph
  let clusterMapping = gatherClusters rigidClusters neighbourMap (IntMap.fromList rigidClusters)

  -- We are going to assign each rigid variable a size expression corresponding to itself.
  let initialSubst = IntMap.fromList (map (\(i, bound) ->
        (i, SEMeet $
          let cluster = i `IntMap.lookup` clusterMapping
          in case cluster of
            Just c | c < arity -> assign c baseSize i
            _ -> baseSize)) rigidContext)
  substitution <- instantiateComponents (SEMeet baseSize) rigidContext clusterMapping adjacencyMap initialSubst sccs
  pure $ (substitution, clusterMapping)

-- | 'gatherClusters layer neighbors result' collects a map from graph nodes (the keys in 'neighbors') to their approximate cluster.
-- This algorithm is BFS, which sweeps over the graph layer by layer (the first argument 'layer', which is a pairing between a variable and its cluster).
-- Initially, the processing starts from rigid variables, for which we know their clusters.
-- 'result' is a storage of the collected clusters and the set of already visited graph nodes simultaneously.
--
-- There is no guarantee that a cluster for a flexible variable can be determined uniquely.
-- However, this mapping is used in heuristics, for which it is allowed to have some approximation.
gatherClusters :: [(Int, Int)] -> IntMap (NonEmpty Int) -> IntMap Int -> IntMap Int
gatherClusters [] _ res = res
gatherClusters list graph res =
  let (combinedMap, combinedNextLevel) = foldr (\(vertex, cluster) (mp, collected) ->
        let surrounding = maybe [] NonEmpty.toList (IntMap.lookup vertex graph)
        in foldr (\neighborVertex (newMp, newEdges) -> if IntMap.member neighborVertex newMp
              then (newMp, newEdges)
              else (IntMap.insert neighborVertex cluster newMp, (neighborVertex, cluster) : newEdges)) (mp, collected) surrounding) (res, []) list
  in gatherClusters combinedNextLevel graph combinedMap

findCluster :: [(Int, SizeBound)] -> Int -> Maybe Int
findCluster rigids i = case List.lookup i rigids of
  Nothing -> Nothing
  Just SizeUnbounded -> Just i
  Just (SizeBounded j) -> findCluster rigids j

-- 'instantiateComponents baseSize rigids clusters adjacencyMap subst sccs' assigns a size expression for each flexible variable occurring in 'sccs'.
-- It is mandatory that 'sccs' is sorted in topological order according to 'adjacencyMap'.
instantiateComponents :: SizeExpression -> [(Int, SizeBound)] -> IntMap Int -> DGraph.Graph Int ConstrType -> IntMap SizeExpression -> [NonEmpty Int] -> MonadSizeChecker (IntMap SizeExpression)
instantiateComponents _ _ _ graph subst [] = pure subst
instantiateComponents baseSize rigids clusterMapping graph subst (comp@(hd :| tl) : is) = do

  bottomVars <- MSC $ gets scsBottomFlexVars
  globalMinimum <- MSC $ gets scsLeafSizeVariables
  undefinedVars <- getUndefinedSizes
  fallback <- MSC $ gets scsFallbackInstantiations

  let (lowerBounds, inComponentEdges) = partitionEithers $ map (\(DGraph.Edge bigger lower constr) ->
        if (lower `List.elem` comp)
        then Right constr
        else Left (constr, lower)) (DGraph.edgesFrom graph (NonEmpty.toList comp))
  let lowerBoundSizes = map (\(a, x) -> (a, fromMaybe baseSize (subst IntMap.!? x))) lowerBounds


  -- Let's try to guess an instantiation of a component of flexible variables
  let assignedSize
        | (any (== SLte) inComponentEdges) =
          -- So there is a constraint of type '<' in a strongly connected component
          -- Which implies that the component should be assigned to infinity, as we essentially have 'a < a'
          baseSize
        | (any (`IntSet.member` undefinedVars) comp) =
           -- Some element in the component has is bigger or equal than infinity,
           -- which means that the component should be assigned to infinity
           baseSize
        | hd `IntSet.member` bottomVars =
          -- The component corresponds to a non-recursive constructor,
          -- which means that it should be assigned to the least available size expression,
          -- which is a meet of certain rigids
          SEMeet globalMinimum
        | null lowerBoundSizes =
          -- There are no lower bounds for the component, which means that we can try to do some witchcraft
          -- It won't be worse than infinity, right?
          case (IntMap.lookup hd fallback, (hd `IntMap.lookup` clusterMapping)) of
            (Just r, _) ->
              -- The component corresponds to a freshened variable of some recursive call, we can try to assign it to the original variable
              fromMaybe baseSize (subst IntMap.!? r)
            (Nothing, Just cluster) -> do
              -- We managed to find a cluster for a variable, which means that we can try to assign a variable to the lowest available rigid in a cluster
                let lowestCluster = findLowestClusterVariable rigids cluster
                fromMaybe baseSize (subst IntMap.!? lowestCluster)
              -- The witchcraft failed, we assign the component to infinity
            (Nothing, Nothing) -> baseSize
        | otherwise =
          -- So there are some lower bounds, let's assign the least upper bound of all lower bounds to this component
          foldr1 leastUpperBound (map (uncurry findSuitableSize) lowerBoundSizes)

  let newSubst = IntMap.union subst (IntMap.fromList (map (, assignedSize) (NonEmpty.toList comp)))
  reportSDoc "term.tbt" 70 $ "Component:" <+> text (show comp) <+>
                             ", lower bound sizes:" <+> pure (P.pretty lowerBoundSizes) <+>
                             ", lower bounds: " <+> pure (P.pretty lowerBounds) <+>
                             ", assignedSize: " <+> pure (P.pretty assignedSize) <+>
                             ", bottom vars: " <+> text (show bottomVars)

  instantiateComponents baseSize rigids clusterMapping graph newSubst is
  where
    -- Searches for a suitable size expression in a list of known size bounds
    findSuitableSize :: ConstrType -> SizeExpression -> SizeExpression
    findSuitableSize SLeq se = se
    findSuitableSize SLte (SEMeet exp) = SEMeet $ map (\i -> if i == -1 then -1 else case List.lookup i rigids of
      Nothing -> -1
      Just SizeUnbounded -> -1
      Just (SizeBounded j) -> j) exp

    -- Computes LUB for two sizes. If the sizes are defined, then it is LCA in the tree of comparisons.
    -- This is in fact list intersection
    leastUpperBound :: SizeExpression -> SizeExpression -> SizeExpression
    leastUpperBound (SEMeet l1) (SEMeet l2) = SEMeet (List.zipWith min l1 l2)

-- Sets an element in a list
assign :: Int -> [Int] -> Int -> [Int]
assign 0 (x : xs) e = e : xs
assign n (x : xs) e = x : (assign (n - 1) xs e)
assign n xs i = __IMPOSSIBLE__

-- Tries to find the deepest variable in the set of rigids for a given cluster
findLowestClusterVariable :: [(Int, SizeBound)] -> Int -> Int
findLowestClusterVariable bounds target = fst $ go 0 target
  where
    go :: Int -> Int -> (Int, Int)
    go depth target =
      let nextLevel = mapMaybe (\(i, bound) -> case bound of
            SizeBounded j | j == target -> Just i
            _ -> Nothing) (bounds)
      in foldr (\(nt, nd) (ct, cd) -> if nd > cd then (nt, nd) else (ct, cd)) (target, depth) (map (go (depth + 1)) nextLevel)

collectIncoherentRigids :: IntMap SizeExpression -> [SConstraint] -> TCM IntSet
collectIncoherentRigids m g = billTo [Benchmark.TypeBasedTermination, Benchmark.SizeGraphSolving] $ collectIncoherentRigids' m g

-- | A rigid variable is incoherent if it has lower bound of infinity.
--   In particular it means that there is something wrong with the graph,
--   and the incoherent rigids should not be used for termination checking.
collectIncoherentRigids' :: IntMap SizeExpression -> [SConstraint] -> TCM IntSet
collectIncoherentRigids' subst [] = pure IntSet.empty
collectIncoherentRigids' subst ((SConstraint sctype from to) : rest) = do
  let fromExpr = subst IntMap.!? from
      toExpr = subst IntMap.!? to
      incoherences = getIncoherences fromExpr toExpr
  unless (null incoherences) $ do
    reportSDoc "term.tbt" 70 $ "Incoherence detected: (" <> pretty from <> "," <> pretty to <> ") -> " <> pretty fromExpr <> "," <> pretty toExpr
  IntSet.union (IntSet.fromList incoherences) <$> (collectIncoherentRigids' subst rest)

getIncoherences :: Maybe SizeExpression -> Maybe SizeExpression -> [Int]
getIncoherences  (Just (SEMeet l)) (Just (SEMeet r)) | (all (== (-1)) l) = mapMaybe (\(ls, rs) -> if ls == (-1) && rs /= (-1) then Just rs else Nothing) (zip l r)
getIncoherences _ _ = []
