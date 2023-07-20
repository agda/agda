{-| SplitClause and CoverResult types.
 -}

module Agda.TypeChecking.Coverage.SplitClause where

import Prelude hiding (null, (!!))  -- do not use partial functions like !!

import Data.Map (Map)
import qualified Data.Map as Map
import qualified Data.Set as Set
import Data.IntSet (IntSet)
import qualified Data.IntSet as IntSet

import Agda.Syntax.Common
import Agda.Syntax.Internal hiding (DataOrRecord(..))

import Agda.TypeChecking.Coverage.Match
import Agda.TypeChecking.Coverage.SplitTree
import Agda.TypeChecking.Monad
import Agda.TypeChecking.Substitute

data SplitClause = SClause
  { scTel    :: Telescope
    -- ^ Type of variables in @scPats@.
  , scPats   :: [NamedArg SplitPattern]
    -- ^ The patterns leading to the currently considered branch of
    --   the split tree.
  , scSubst  :: Substitution' SplitPattern
    -- ^ Substitution from 'scTel' to old context.
    --   Only needed directly after split on variable:
    --   * To update 'scTarget'
    --   * To rename other split variables when splitting on
    --     multiple variables.
    --   @scSubst@ is not ``transitive'', i.e., does not record
    --   the substitution from the original context to 'scTel'
    --   over a series of splits.  It is freshly computed
    --   after each split by 'computeNeighborhood'; also
    --   'splitResult', which does not split on a variable,
    --   should reset it to the identity 'idS', lest it be
    --   applied to 'scTarget' again, leading to Issue 1294.
  , scCheckpoints :: Map CheckpointId Substitution
    -- ^ We need to keep track of the module parameter checkpoints for the
    -- clause for the purpose of inferring missing instance clauses.
  , scTarget :: Maybe (Dom Type)
    -- ^ The type of the rhs, living in context 'scTel'.
    --   'fixTargetType' computes the new 'scTarget' by applying
    --   substitution 'scSubst'.
  }

data UnifyEquiv = UE { infoTel0 :: Telescope          -- Γ0
                     , infoTel :: Telescope           -- Γ'
                     , infoEqTel :: Telescope         -- Γ0 ⊢ Δ
                     , infoEqLHS :: [Term]            -- Γ0 ⊢ us : Δ
                     , infoEqRHS :: [Term]            -- Γ0 ⊢ vs : Δ
                     , infoRho :: PatternSubstitution -- Γ' ⊢ ρ : Γ0
                                                      -- Γ = Γ0,(φ : I),(eqs : Paths Δ us vs)
                                                      -- Γ' ⊢ ρ,i1,refls : Γ
                     , infoTau :: Substitution        -- Γ  ⊢ τ           : Γ'
                     , infoLeftInv :: Substitution    -- Γ | (i : I) ⊢ leftInv : Γ
                     -- leftInv[i=0] = ρ[τ],i1s,refls
                     -- leftInv[i=1] = idS
                     }
                  deriving Show

data IInfo = TheInfo UnifyEquiv | NoInfo deriving Show

-- | A @Covering@ is the result of splitting a 'SplitClause'.
data Covering = Covering
  { covSplitArg     :: Arg Nat
     -- ^ De Bruijn level (counting dot patterns) of argument we split on.
  , covSplitClauses :: [(SplitTag, (SplitClause, IInfo))]
      -- ^ Covering clauses, indexed by constructor/literal these clauses share.
  }

-- | Project the split clauses out of a covering.
splitClauses :: Covering -> [SplitClause]
splitClauses (Covering _ qcs) = map (fst . snd) qcs

-- | Create a split clause from a clause in internal syntax. Used by make-case.
clauseToSplitClause :: Clause -> SplitClause
clauseToSplitClause cl = SClause
  { scTel    = clauseTel cl
  , scPats   = toSplitPatterns $ namedClausePats cl
  , scSubst  = idS  -- Andreas, 2014-07-15  TODO: Is this ok?
  , scCheckpoints = Map.empty -- #2996: not __IMPOSSIBLE__ for debug printing
  , scTarget = domFromArg <$> clauseType cl
  }


---------------------------------------------
-- Record type for the results of @cover@
---------------------------------------------

data CoverResult = CoverResult
  { coverSplitTree       :: SplitTree
  , coverUsedClauses     :: IntSet -- Set Nat
  , coverMissingClauses  :: [(Telescope, [NamedArg DeBruijnPattern])]
  , coverPatterns        :: [Clause]
  -- ^ The set of patterns used as cover.
  , coverNoExactClauses  :: IntSet -- Set Nat
  }
