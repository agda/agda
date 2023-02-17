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

-- A size expression is represented as a minimum of a set of rigid size variables,
-- where the length of the set is equal to the number of clusters.
newtype SizeExpression = SEMeet [Int]
  deriving Eq

instance Show SizeExpression where
  show (SEMeet list) = case filter (/= (-1)) list of
    [] -> "∞"
    nonempty -> List.intercalate " ∧ " (map (\i -> show (SDefined i)) nonempty)

type GraphEnv a = StateT SizeCheckerState TCM a

-- | 'simplifySizeGraph _ context graph' assigns all variables occurring in the graph to the variables from the context
-- The outline:
-- 1. Find all strongly connected components. If they behave bad (have edge <), then instantiate them all to infinity. TODO
-- 2. Sort the obtained acyclic graph topologically.
-- 3. For each component in the order, assign the least upper bound of all known lower bounds. If there are no lower bounds, apply a heuristic.
simplifySizeGraph :: Bool -> [(Int, SizeBound)] -> [SConstraint] -> MonadSizeChecker (IntMap SizeExpression)
simplifySizeGraph verbose rigidContext graph = do
  let sccs = computeSCCs rigidContext graph
  currentRoot <- currentCheckedName
  -- The arity corresponds to the number of clusters
  arity <- getArity currentRoot
  let baseSize = replicate arity (-1)
  bottomVars <- MSC $ gets scsBottomFlexVars
  contra <- getContravariantSizeVariables
  when verbose $ reportSDoc "term.tbt" 40 $ vcat $ map (nest 2)
    [ "Order:               " <+> text (show graph)
    , "Rigid context:       " <+> text (show rigidContext)
    , "Bottom vars:         " <+> text (show bottomVars)
    , "Arity:               " <+> text (show arity)
    , "Contravariant:       " <+> text (show contra)
    , "baseSize:            " <+> text (show baseSize)
    , "clusters:            " <+> (vcat $ (map (\i -> text $ (show (SDefined i)) ++ " has cluster: " ++ show (findCluster rigidContext graph i)) (map fst rigidContext)))
    ]
  -- We are going to assign each rigid variable a size expression corresponding to itself.
  let initialSubst = IntMap.fromList (map (\(i, bound) ->
        (i, SEMeet $
          let cluster = findCluster rigidContext graph i
          in case cluster of
            Just c | c < arity -> assign c baseSize i
            _ -> baseSize)) rigidContext)
  instantiateComponents verbose arity rigidContext graph initialSubst sccs

-- | This function tries to guess cluster across entire graph, since some of the variables may contain a flexible variable as an upper bound
-- This is the case when a flexible variable is obtained through a projection.
findCluster :: [(Int, SizeBound)] -> [SConstraint] -> Int -> Maybe Int
findCluster rigids constraints = fst . findCluster' rigids constraints IntSet.empty
  where
    findCluster' :: [(Int, SizeBound)] -> [SConstraint] -> IntSet -> Int -> (Maybe Int, IntSet)
    findCluster' rigids constraints visited vertex | vertex `List.elem` (map fst rigids) = case List.lookup vertex rigids of
      Just (SizeBounded i) -> findCluster' rigids constraints (IntSet.insert vertex visited) i
      Just (SizeUnbounded) -> (Just vertex, visited)
      Nothing -> __IMPOSSIBLE__
    findCluster' rigids constraints visited vertex | IntSet.member vertex visited = (Nothing, visited)
    findCluster' rigids constraints visited vertex | otherwise =
      let upperBounds = mapMaybe (\(SConstraint _ from to) -> if from == vertex then Just to else Nothing) constraints
          lowerBounds = mapMaybe (\(SConstraint _ from to) -> if to == vertex then Just from else Nothing) constraints
          foldVertices = foldr (\lb (res, visited') -> case res of
            Just i -> (Just i, visited')
            Nothing -> findCluster' rigids constraints visited' lb)
      in foldVertices (foldVertices (Nothing, (IntSet.insert vertex visited)) lowerBounds) upperBounds

-- For each flexible size variable in the list (last argument), assignes a size expression
instantiateComponents :: Bool -> Int -> [(Int, SizeBound)] -> [SConstraint] -> IntMap SizeExpression -> [[Int]] -> MonadSizeChecker (IntMap SizeExpression)
instantiateComponents verbose arity rigids constraints subst [] = pure subst
instantiateComponents verbose arity rigids constraints subst (comp : is) = do

  bottomVars <- MSC $ gets scsBottomFlexVars
  globalMinimum <- MSC $ gets scsLeafSizeVariables
  undefinedVars <- getUndefinedSizes
  fallback <- MSC $ gets scsFallbackInstantiations

  let baseSize = (SEMeet (replicate arity (-1)))
  let lowerBounds = mapMaybe (\constr ->
        if scTo constr `List.elem` comp &&
          (not $ scFrom constr `List.elem` comp)
        then Just (scType constr, scFrom constr)
        else Nothing) constraints
  let lowerBoundSizes = map (\(a, x) -> (a, fromMaybe baseSize (subst IntMap.!? x))) lowerBounds


  -- Let's try to guess an instantiation of a component of flexible variables
  let assignedSize
        | (any (`IntSet.member` undefinedVars) comp) =
           -- Some element in the component has is bigger or equal than infinity,
           -- which means that the component should be assigned to infinity
           baseSize
        | head comp `IntSet.member` bottomVars =
          -- The component corresponds to a non-recursive constructor,
          -- which means that it should be assigned to the least available size expression,
          -- which is a meet of certain rigids
          SEMeet globalMinimum
        | null lowerBoundSizes =
          -- There are no lower bounds for the component, which means that we can try to do some witchcraft
          case (IntMap.lookup (head comp) fallback, (findCluster rigids constraints (head comp))) of
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

  let newSubst = IntMap.union subst (IntMap.fromList (map (, assignedSize) comp))
  when verbose $ reportSDoc "term.tbt" 20 $ "component:" <+> text (show comp) <+> ", lower bound sizes:" <+> text (show lowerBoundSizes) <+> ",lower bounds: " <+> text (show lowerBounds) <+> ", assignedSize: " <+> text (show assignedSize) <+> ", bottom vars: " <+> text (show bottomVars)

  instantiateComponents verbose arity rigids constraints newSubst is
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
assign n xs i = trace ("n : " ++ show n ++ ", length xs: " ++ show (length xs) ++ ", i: " ++ show i) undefined

computeSCCs :: [(Int, SizeBound)] -> [SConstraint] -> [[Int]]
computeSCCs rigidContext graph =
  let adj = foldr (\c graph -> IntMap.insertWith (\a b -> b) (scFrom c) []
                              (IntMap.insert                 (scTo c)   (scFrom c : IntMap.findWithDefault [] (scTo c) graph) graph))
                  IntMap.empty graph
      assocList = map (\(a, b) -> (a, a, b)) (IntMap.toAscList adj)
  in map Graph.flattenSCC $ Graph.stronglyConnComp (filter (\(a, _, _) -> not (a `List.elem` (map fst rigidContext))) assocList)

-- Given a set of rigids, tries to find the deepest variable in the set of rigids for a given cluster
findLowestClusterVariable :: [(Int, SizeBound)] -> Int -> Int
findLowestClusterVariable bounds target = fst $ go 0 target
  where
    go :: Int -> Int -> (Int, Int)
    go depth target =
      let nextLevel = mapMaybe (\(i, bound) -> case bound of
            SizeBounded j | j == target -> Just i
            _ -> Nothing) (bounds)
      in case nextLevel of
            [] -> (target, depth)
            l -> let inner = map (go (depth + 1)) l
                     maxLevel = maximum (map snd inner)
                     maxLevelVars = filter (\(a, d) -> d == maxLevel) inner
                 in head maxLevelVars

-- | A rigid variable is incoherent if it has lower bound of infinity.
--   In particular it means that there is something wrong with the graph,
--   and the incoherent rigids should not be used for termination checking.
collectIncoherentRigids :: IntMap SizeExpression -> [SConstraint] -> TCM IntSet
collectIncoherentRigids subst [] = pure IntSet.empty
collectIncoherentRigids subst ((SConstraint sctype from to) : rest) = do
  let fromExpr = subst IntMap.!? from
      toExpr = subst IntMap.!? to
      incoherences = getIncoherences fromExpr toExpr
  unless (null incoherences) $ do
    reportSDoc "term.tbt" 20 $ text ("Incoherence detected: (" ++ show from ++ "," ++ show to ++ ") -> " ++ show fromExpr ++ "," ++ show toExpr)
  IntSet.union (IntSet.fromList incoherences) <$> (collectIncoherentRigids subst rest)

getIncoherences :: Maybe SizeExpression -> Maybe SizeExpression -> [Int]
getIncoherences  (Just (SEMeet l)) (Just (SEMeet r)) | (all (== (-1)) l) = mapMaybe (\(ls, rs) -> if ls == (-1) && rs /= (-1) then Just rs else Nothing) (zip l r)
getIncoherences _ _ = []
