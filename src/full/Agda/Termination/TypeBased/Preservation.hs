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
module Agda.Termination.TypeBased.Preservation
  ( refinePreservedVariables
  , applySizePreservation
  ) where

import Control.Arrow (second)
import Control.Monad ( forM )
import Data.Foldable (traverse_)
import Data.Functor ((<&>))
import Data.IntMap ( IntMap )
import qualified Data.IntMap as IntMap
import qualified Data.IntSet as IntSet
import Data.IntSet ( IntSet )
import qualified Data.List as List
import Data.Maybe ( mapMaybe )

import Agda.Termination.TypeBased.Common (VariableInstantiation(..), reifySignature)
import Agda.Termination.TypeBased.Graph ( SizeExpression, simplifySizeGraph, collectIncoherentRigids, collectClusteringIssues )
import Agda.Termination.TypeBased.Monad ( SConstraint(SConstraint), getCurrentConstraints, getCurrentRigids, currentCheckedName, withAnotherPreservationCandidate, TBTM, getPreservationCandidates, getRecursionMatrix, replacePreservationCandidates )
import Agda.Termination.TypeBased.Syntax ( SizeSignature(SizeSignature), SizeBound, SizeType(..), Size(..) )
import Agda.TypeChecking.Monad.Base ( MonadTCM(liftTCM), sizePreservationOption )
import Agda.TypeChecking.Monad.Debug ( reportSDoc )
import Agda.TypeChecking.Pretty ( PrettyTCM(prettyTCM), pretty, nest, ($$), (<+>), vcat, text )


-- | This function is expected to be called after finishing the processing of clause,
-- or, more generally, after every step of collecting complete graph of dependencies between flexible sizes.
-- It looks at each possibly size-preserving variable and filters its candidates
-- such that after the filtering all remaining candidates satisfy the current graph.
-- By induction, when the processing of a function ends, all remaining candidates satisfy all clauses' graphs.
refinePreservedVariables :: TBTM ()
refinePreservedVariables = do
  rigids <- getCurrentRigids
  graph <- getCurrentConstraints
  varsAndCandidates <- IntMap.toAscList <$> getPreservationCandidates
  newMap <- forM varsAndCandidates (\(possiblyPreservingVar, candidates) -> do
    refinedCandidates <- refineCandidates candidates graph rigids possiblyPreservingVar
    pure (possiblyPreservingVar, refinedCandidates))
  let refinedMap = IntMap.fromAscList newMap
  reportSDoc "term.tbt" 70 $ "Refined candidates:" <+> text (show refinedMap)
  replacePreservationCandidates (IntMap.fromAscList newMap)

-- | Eliminates the candidates that do not satisfy the provided graph of constraints.
refineCandidates :: [Int] -> [SConstraint] -> [(Int, SizeBound)] -> Int -> TBTM [Int]
refineCandidates candidates graph rigids possiblyPreservingVar = do
  result <- forM candidates $ \candidate -> do
    checkCandidateSatisfiability possiblyPreservingVar candidate graph rigids
  let suitableCandidate = mapMaybe (\(candidate, isFine) -> if isFine then Just candidate else Nothing) (zip candidates result)
  reportSDoc "term.tbt" 70 $ "Suitable candidates for " <+> text (show possiblyPreservingVar) <+> "is" <+> text (show suitableCandidate)
  pure suitableCandidate

-- 'checkCandidateSatisfiability possiblyPreservingVar candidateVar graph bounds' returns 'True' if
-- 'possiblyPreservingVar' and 'candidateVarChecks' can be treates as the same within 'graph'.
checkCandidateSatisfiability :: Int -> Int -> [SConstraint] -> [(Int, SizeBound)] -> TBTM Bool
checkCandidateSatisfiability possiblyPreservingVar candidateVar graph bounds = do
  reportSDoc "term.tbt" 70 $ "Trying to replace " <+> text (show possiblyPreservingVar) <+> "with" <+> text (show candidateVar)

  matrix <- getRecursionMatrix
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
  substitution <- withAnotherPreservationCandidate candidateVar $ simplifySizeGraph bounds mappedGraph
  incoherences <- liftTCM $ collectIncoherentRigids substitution mappedGraph
  let allIncoherences = IntSet.union incoherences $ collectClusteringIssues candidateVar substitution mappedGraph bounds
  reportSDoc "term.tbt" 70 $ "Incoherences during an attempt:" <+> text (show allIncoherences)
  pure $ not $ IntSet.member candidateVar allIncoherences



-- | Applies the size preservation analysis result to a function signature.
applySizePreservation :: SizeSignature -> TBTM SizeSignature
applySizePreservation s@(SizeSignature _ _ tele) = do
  candidates <- getPreservationCandidates
  isPreservationEnabled <- sizePreservationOption
  flatCandidates <- forM (IntMap.toAscList candidates) (\(replaceable, candidates) -> (replaceable,) <$> case candidates of
        [unique] -> do
          reportSDoc "term.tbt" 40 $ "Assigning" <+> text (show replaceable) <+> "to" <+> text (show unique)
          pure $ if isPreservationEnabled then ToVariable unique else ToInfinity
        (_ : _) -> do
          -- Ambiguous situation, we would rather not assign anything here at all
          reportSDoc "term.tbt" 60 $ "Multiple candidates for variable" <+> text (show replaceable)
          pure ToInfinity
        [] -> do
          -- No candidates means that the size of variable is much bigger than any of codomain
          -- This can happen in the function 'add : Nat -> Nat -> Nat' for example.
          reportSDoc "term.tbt" 60 $ "No candidates for variable " <+> text (show replaceable)
          pure ToInfinity)
  let newSignature = reifySignature flatCandidates s
  currentName <- currentCheckedName
  reportSDoc "term.tbt" 5 $ "Signature of" <+> prettyTCM currentName <+> "after size-preservation inference:" $$ nest 2 (pretty newSignature)
  pure newSignature
