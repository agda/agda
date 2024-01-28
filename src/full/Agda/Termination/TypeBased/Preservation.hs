{- | This module contains the machinery for inference of size preservation.

     By default, all signatures for functions use distinct size variables.
     Sometimes the variables are not really distinct, and some dependencies between them can be established.
     As an example, consider a function 'length : List A -> Nat'.
     Given a list built from 'n' constructors 'cons', it returns a natural number build from 'n' constructors 'suc'.
     In some sense, 'length' preserves the size of input list in its output natural number.

     Size preservation is a generalization of this idea.
     Initially, it is based on a hypothesis that some codomain size variables are the same as certain domain size variables,
     so the algorithm in this file tries to prove or disprove these hypotheses.
     The actual implementation is rather simple: the algorithm just tries to apply each hypothesis and then check if the constraint graph still behaves well,
     i.e. if there are no cycles with infinities for rigid variables.

     The variables that could be dependent on some other ones are called _possibly size-preserving_ here,
     and the variables that can be the source of dependency are called _candidates_.
     Each possibly size-preserving variable has its own set of candidates.

     It is also worth noting that the coinductive size preservation works dually to the inductive one.
     In the inductive case, we are trying to find out if some codomain sizes are the same as the domain ones,
     and the invariant here is that all domain sizes are independent.
     In the coinductive case, we have a codomain size, and we are trying to check whether some of the domain sizes are equal to this codomain.
     Assume a function 'zipWith : (A -> B -> C) -> Stream A -> Stream B -> Stream C'.
     This function is size-preserving in both its coinductive arguments, since it applies the same amount of projections to arguments as it was asked for the result.
 -}
module Agda.Termination.TypeBased.Preservation where

import Agda.Syntax.Internal.Pattern
import Agda.Termination.TypeBased.Syntax
import Control.Monad.Trans.State
import Agda.TypeChecking.Monad.Base
import Agda.TypeChecking.Monad.Statistics
import Agda.TypeChecking.Monad.Debug
import Agda.TypeChecking.Monad.Signature
import Agda.Syntax.Common
import qualified Data.Map as Map
import Data.Map ( Map )
import qualified Data.IntMap as IntMap
import Data.IntMap ( IntMap )
import qualified Data.IntSet as IntSet
import Data.IntSet ( IntSet )
import qualified Data.Set as Set
import Data.Set ( Set )
import qualified Data.List as List
import Agda.Syntax.Abstract.Name
import Control.Monad.IO.Class
import Control.Monad.Trans
import Agda.TypeChecking.Monad.Env
import Agda.TypeChecking.Reduce
import Agda.TypeChecking.Monad.Context
import Agda.TypeChecking.Telescope
import Agda.Termination.TypeBased.Common
import Agda.TypeChecking.Substitute
import Agda.Termination.TypeBased.Monad
import Agda.TypeChecking.ProjectionLike
import Agda.Utils.Impossible
import Agda.Termination.TypeBased.Checking
import Control.Monad
import Agda.TypeChecking.Pretty
import Debug.Trace
import Agda.Utils.Monad
import Agda.Termination.Common
import Data.Maybe
import Agda.Termination.TypeBased.Encoding
import Agda.Termination.CallGraph
import Agda.Termination.Monad
import Agda.Termination.TypeBased.Graph
import Data.Foldable (traverse_)
import Agda.Utils.List ((!!!))
import Data.Functor ((<&>))
import Agda.Termination.CallMatrix
import qualified Agda.Termination.CallMatrix
import Agda.Utils.Graph.AdjacencyMap.Unidirectional (Edge(..))
import Data.Either
import Agda.Utils.Singleton
import Agda.Termination.Order (Order)
import qualified Agda.Termination.Order as Order

-- | Populates the sets of possibly size-preserving variables in a function.
initSizePreservationStructure :: SizeType -> MonadSizeChecker ()
initSizePreservationStructure tele = do
  let (_, codomain) = sizeCodomain tele
  let codomainVariables = gatherCodomainVariables codomain
  let minimalVar = case codomainVariables of
        [] -> 0
        _ -> minimum codomainVariables
  coinductiveVars <- getContravariantSizeVariables
  let (coinductiveDomain, inductiveDomain) = List.partition (`IntSet.member` coinductiveVars) [0..minimalVar - 1]
  let (coinductiveCodomain, inductiveCodomain) = List.partition (`IntSet.member` coinductiveVars) codomainVariables
  let zipped = (map (, coinductiveCodomain) coinductiveDomain) -- instantiating coinductive domain to coinductive codomain
               ++
               (map (, inductiveDomain) inductiveCodomain) -- instantiating inductive codomain to inductive domain
  let candidates = IntMap.fromList zipped
  reportSDoc "term.tbt" 40 $ "Size preservation candidates: " <> pretty candidates
  MSC $ modify (\s -> s { scsPreservationCandidates = IntMap.fromList zipped })
  where
    -- Collects a set of variables that are used in the codomain of the function.
    gatherCodomainVariables :: SizeType -> [Int]
    gatherCodomainVariables (SizeTree s rest) = (case s of
      SDefined i -> [i]
      SUndefined -> []) ++ concatMap gatherCodomainVariables rest
    gatherCodomainVariables (SizeArrow l r) = gatherCodomainVariables l ++ gatherCodomainVariables r
    gatherCodomainVariables (SizeGeneric _ r) = gatherCodomainVariables r
    gatherCodomainVariables (SizeGenericVar _ _) = []

-- | This function is expected to be called after finishing the processing of clause,
-- or, more generally, after every step of collecting complete graph of dependencies between flexible sizes.
-- It looks at each possibly size-preserving variable and filters its candidates
-- such that after the filtering all remaining candidates satisfy the current graph.
-- By induction, when the processing of a function ends, all remaining candidates satisfy all clause's graphs.
refinePreservedVariables :: MonadSizeChecker ()
refinePreservedVariables = do
  rigids <- getCurrentRigids
  graph <- getCurrentConstraints
  varsAndCandidates <- MSC $ IntMap.toAscList <$> gets scsPreservationCandidates
  newMap <- forM varsAndCandidates (\(possiblyPreservingVar, candidates) -> do
    refinedCandidates <- refineCandidates candidates graph rigids possiblyPreservingVar
    pure (possiblyPreservingVar, refinedCandidates))
  let refinedMap = IntMap.fromAscList newMap
  reportSDoc "term.tbt" 70 $ "Refined candidates:" <+> text (show refinedMap)
  MSC $ modify (\s -> s { scsPreservationCandidates = IntMap.fromAscList newMap })

-- | Eliminates the candidates that do not satisfy the provided graph of constraints.
refineCandidates :: [Int] -> [SConstraint] -> [(Int, SizeBound)] -> Int -> MonadSizeChecker [Int]
refineCandidates candidates graph rigids possiblyPreservingVar = do
  result <- forM candidates $ \candidate -> do
    checkCandidateSatisfiability possiblyPreservingVar candidate graph rigids
  let suitableCandidate = mapMaybe (\(candidate, isFine) -> if isFine then Just candidate else Nothing) (zip candidates result)
  reportSDoc "term.tbt" 70 $ "Suitable candidates for " <+> text (show possiblyPreservingVar) <+> "is" <+> text (show suitableCandidate)
  pure suitableCandidate

-- 'checkCandidateSatisfiability possiblyPreservingVar candidateVar graph bounds' returns 'True' if
-- 'possiblyPreservingVar' and 'candidateVarChecks' can be treates as the same within 'graph'.
checkCandidateSatisfiability :: Int -> Int -> [SConstraint] -> [(Int, SizeBound)] -> MonadSizeChecker Bool
checkCandidateSatisfiability possiblyPreservingVar candidateVar graph bounds = do
  reportSDoc "term.tbt" 70 $ "Trying to replace " <+> text (show possiblyPreservingVar) <+> "with" <+> text (show candidateVar)

  matrix <- MSC $ gets scsRecCallsMatrix
  -- Now we are trying to replace all variables in 'replaceableCol' with variables in 'replacingCol'
  let replaceableCol = possiblyPreservingVar : map (List.!! possiblyPreservingVar) matrix
  let replacingCol = candidateVar : map (List.!! candidateVar) matrix
  -- For each recursive call, replaces recursive call's possibly-preserving variable with its candidate in the same call.
  let graphVertexSubstitution = (\i -> case List.elemIndex i replaceableCol of { Nothing -> i; Just j -> replacingCol List.!! j })
  let mappedGraph = map (\(SConstraint t l r) -> SConstraint t (graphVertexSubstitution l) (graphVertexSubstitution r)) graph
  reportSDoc "term.tbt" 70 $ vcat
    [ "Mapped graph: " <+> text (show mappedGraph)
    , "codomainCol:  " <+> text (show replaceableCol)
    , "domainCol:    " <+> text (show replacingCol)
    ]

  -- Now let's see if there are any problems if we try to solve graph with merged variables.
  (substitution, clusterMapping) <- simplifySizeGraph bounds mappedGraph
  incoherences <- liftTCM $ collectIncoherentRigids substitution mappedGraph
  let allIncoherences = IntSet.union incoherences $ collectClusteringIssues candidateVar clusterMapping mappedGraph bounds
  reportSDoc "term.tbt" 70 $ "Incoherences during an attempt:" <+> text (show incoherences)
  pure $ not $ IntSet.member candidateVar allIncoherences

-- | Since any two clusters are unrelated, having a dependency between them indicates that something is wrong in the graph
collectClusteringIssues :: Int -> (IntMap Int) -> [SConstraint] -> [(Int, SizeBound)] -> IntSet
collectClusteringIssues candidateVar clusters [] bounds = IntSet.empty
collectClusteringIssues candidateVar clusters ((SConstraint _ f t) : rest) bounds | f == candidateVar || t == candidateVar =
  case (List.lookup f bounds, List.lookup t bounds) of
    (Just _, Just _) | IntMap.lookup f clusters /= IntMap.lookup t clusters -> IntSet.insert candidateVar IntSet.empty
    _ -> collectClusteringIssues candidateVar clusters rest bounds
collectClusteringIssues candidateVar totalGraph (_ : rest) bounds = collectClusteringIssues candidateVar totalGraph rest bounds

-- | Applies the size preservation analysis result to the function signature
applySizePreservation :: SizeSignature -> MonadSizeChecker SizeSignature
applySizePreservation s@(SizeSignature _ _ tele) = do
  candidates <- MSC $ gets scsPreservationCandidates
  isPreservationEnabled <- sizePreservationOption
  flatCandidates <- forM (IntMap.toAscList candidates) (\(replaceable, candidates) -> (replaceable,) <$> case candidates of
        [unique] -> do
          reportSDoc "term.tbt" 40 $ "Assigning" <+> text (show replaceable) <+> "to" <+> text (show unique)
          pure $ if isPreservationEnabled then Just unique else Nothing
        (_ : _) -> do
          -- Ambiguous situation, we would rather not assign anything here at all
          reportSDoc "term.tbt" 60 $ "Multiple candidates for variable" <+> text (show replaceable)
          pure Nothing
        [] -> do
          -- No candidates means that the size of variable is much bigger than any of codomain
          -- This can happen in the function 'add : Nat -> Nat -> Nat' for example.
          reportSDoc "term.tbt" 60 $ "No candidates for variable " <+> text (show replaceable)
          pure Nothing)
  let newSignature = reifySignature flatCandidates s
  currentName <- currentCheckedName
  reportSDoc "term.tbt" 5 $ "Signature of" <+> prettyTCM currentName <+> "after size-preservation inference:" $$ nest 2 (pretty newSignature)
  pure newSignature

-- | Actually applies size preservation assignment to a signature.
--
-- The input list must be ascending in keys.
reifySignature :: [(Int, Maybe Int)] -> SizeSignature -> SizeSignature
reifySignature mapping (SizeSignature bounds contra tele) =
  let newBounds = take (length bounds - length mapping) bounds
      offset x = length (filter (< x) (map fst mapping))
      actualOffsets = IntMap.fromAscList (zip [0..] (List.unfoldr (\(ind, list) ->
        case list of
            [] -> if ind < length bounds then Just (Just (ind - offset ind), (ind + 1, [])) else Nothing
            ((i1, i2) : ps) ->
                 if i1 == ind
                    then Just ((\i -> i - offset i) <$> i2 , (ind + 1, ps))
                    else Just (Just (ind - offset ind), (ind + 1, list)))
        (0, mapping)))
      newSig = (SizeSignature newBounds (List.nub (mapMaybe (actualOffsets IntMap.!) contra)) (fixSizes (actualOffsets IntMap.!) tele))
  in newSig
  where
    fixSizes :: (Int -> Maybe Int) -> SizeType -> SizeType
    fixSizes subst (SizeTree size tree) = SizeTree (weakenSize size) (map (fixSizes subst) tree)
      where
        weakenSize :: Size -> Size
        weakenSize SUndefined = SUndefined
        weakenSize (SDefined i) = case subst i of
          Nothing -> SUndefined
          Just j -> SDefined j
    fixSizes subst (SizeArrow l r) = SizeArrow (fixSizes subst l) (fixSizes subst r)
    fixSizes subst (SizeGeneric args r) = SizeGeneric args (fixSizes subst r)
    fixSizes subst (SizeGenericVar args i) = SizeGenericVar args i
