
module Agda.Mimer.Types where

import Control.DeepSeq (NFData)
import Data.Function (on)
import Data.Map (Map)
import GHC.Generics (Generic)

import Agda.Syntax.Abstract (Expr)
import qualified Agda.Syntax.Abstract as A
import Agda.Syntax.Common (InteractionId, Nat)
import Agda.Syntax.Internal

import Agda.TypeChecking.Monad (TCState, CheckpointId, Open, TCEnv)
import Agda.TypeChecking.Substitute (NoSubst)

-- import Agda.Utils.Permutation (idP, permute, takeP)

import Agda.Mimer.Options

import Data.IORef (IORef)

-- Temporary (used for custom cost verbosity hack)
import Agda.Interaction.Base (Rewrite(..))

data MimerResult
  = MimerExpr String -- ^ Returns 'String' rather than 'Expr' because the give action expects a string.
  | MimerClauses QName [A.Clause]
  | MimerList [(Int, String)]
  | MimerNoResult
  deriving (Generic)

instance NFData MimerResult

data SearchBranch = SearchBranch
  { sbTCState :: TCState
  , sbGoals :: [Goal]
  , sbCost :: Int
  , sbCache :: Map CheckpointId ComponentCache
  , sbComponentsUsed :: Map Name Int -- ^ Number of times each component has been used
  }
  deriving (Generic)
instance NFData SearchBranch

-- | NOTE: Equality is only on the fields `sbCost` and `sbGoals`
instance Eq SearchBranch where
  sb1 == sb2 = sbCost sb1 == sbCost sb2 && sbGoals sb1 == sbGoals sb2

-- TODO: Explain
instance Ord SearchBranch where
  compare = compare `on` sbCost

-- Map source component to generated components
type ComponentCache = Map Component (Maybe [Component])

data Goal = Goal
  { goalMeta :: MetaId
  }
  deriving (Generic)
instance NFData Goal

-- TODO: Is this a reasonable Eq instance?
instance Eq Goal where
  g1 == g2 = goalMeta g1 == goalMeta g2

-- | Components that are not changed during search. Components that do change
-- (local variables and let bindings) are stored in each 'SearchBranch'.
data BaseComponents = BaseComponents
  { hintFns :: [Component]
  , hintDataTypes :: [Component]
  , hintRecordTypes :: [Component]
  , hintAxioms :: [Component]
  -- ^ Excluding those producing Level
  , hintLevel :: [Component]
  -- ^ A definition in a where clause
  , hintProjections :: [Component]
  -- ^ Variables that are candidates for arguments to recursive calls
  , hintThisFn :: Maybe Component
  , hintLetVars :: [Open Component]
  , hintRecVars :: Open [(Term, NoSubst Term Int)] -- ^ Variable terms and which argument they come from
  , hintSplitVars :: Open [Term]
  }
  deriving (Generic)

instance NFData BaseComponents

type CompId = Int
data Component = Component
  { compId    :: CompId -- ^ Unique id for the component. Used for the cache.
  , compName  :: Maybe Name -- ^ Used for keeping track of how many times a component has been used
  , compPars  :: Nat -- ^ How many arguments should be dropped (e.g. constructor parameters)
  , compTerm  :: Term
  , compType  :: Type
  , compRec   :: Bool -- ^ Is this a recursive call
  , compMetas :: [MetaId]
  , compCost  :: Cost
  }
  deriving (Eq, Generic)

instance NFData Component

-- TODO: Is this reasonable?
instance Ord Component where
  compare = compare `on` compId

data SearchStepResult
  = ResultExpr Expr
  | ResultClauses [A.Clause]
  | OpenBranch SearchBranch
  | NoSolution
  deriving (Generic)
instance NFData SearchStepResult


data SearchOptions = SearchOptions
  { searchBaseComponents :: BaseComponents
  , searchHintMode :: HintMode
  , searchTimeout :: MilliSeconds
  , searchGenProjectionsLocal :: Bool
  , searchGenProjectionsLet :: Bool
  , searchGenProjectionsExternal :: Bool
  , searchGenProjectionsRec :: Bool
  , searchSpeculateProjections :: Bool
  , searchTopMeta :: MetaId
  , searchTopEnv :: TCEnv
  , searchTopCheckpoint :: CheckpointId
  , searchInteractionId :: InteractionId
  , searchFnName :: Maybe QName
  , searchCosts :: Costs
  , searchStats :: IORef MimerStats
  , searchRewrite :: Rewrite
  , searchBuiltinFlat :: Maybe QName
      -- Cache BUILTIN_FLAT for issue #7662 workaround
  }

type Cost = Int
data Costs = Costs
  { costLocal :: Cost
  , costFn :: Cost
  , costDataCon :: Cost
  , costRecordCon :: Cost
  , costSpeculateProj :: Cost
  , costProj :: Cost
  , costAxiom :: Cost
  , costLet :: Cost
  , costLevel :: Cost
  , costSet :: Cost -- Should probably be replaced with multiple different costs
  , costRecCall :: Cost
  , costNewMeta :: Cost -- ^ Cost of a new meta-variable appearing in a non-implicit position
  , costNewHiddenMeta :: Cost -- ^ Cost of a new meta-variable appearing in an implicit position
  , costCompReuse :: Nat -> Cost -- ^ Cost of reusing a component @n@ times. Only counted when @n>1@.
  }

noCost :: Cost
noCost = 0

defaultCosts :: Costs
defaultCosts = Costs
  { costLocal = 3
  , costFn = 10
  , costDataCon = 3
  , costRecordCon = 3
  , costSpeculateProj = 20
  , costProj = 3
  , costAxiom = 10
  , costLet = 5
  , costLevel = 3
  , costSet = 10
  , costRecCall = 8
  , costNewMeta = 10
  , costNewHiddenMeta = 1
  , costCompReuse = \uses -> 10 * (uses - 1) ^ 2
  }

------------------------------------------------------------------------------
-- * Measure performance
------------------------------------------------------------------------------

data MimerStats = MimerStats
  { statCompHit :: Nat -- ^ Could make use of an already generated component
  , statCompGen :: Nat -- ^ Could use a generator for a component
  , statCompRegen :: Nat -- ^ Had to regenerate the cache (new context)
  , statCompNoRegen :: Nat -- ^ Did not have to regenerate the cache
  , statMetasCreated :: Nat -- ^ Total number of meta-variables created explicitly (not through unification)
  , statTypeEqChecks :: Nat -- ^ Number of times type equality is tested (with unification)
  , statRefineSuccess :: Nat -- ^ Number of times a refinement has been successful
  , statRefineFail :: Nat -- ^ Number of times a refinement has failed
  } deriving (Show, Eq, Generic)
instance NFData MimerStats

emptyMimerStats :: MimerStats
emptyMimerStats = MimerStats
  { statCompHit = 0, statCompGen = 0, statCompRegen = 0 , statCompNoRegen = 0 , statMetasCreated = 0, statTypeEqChecks = 0, statRefineSuccess = 0 , statRefineFail = 0}

incCompHit, incCompGen, incCompRegen, incCompNoRegen, incMetasCreated, incTypeEqChecks, incRefineSuccess, incRefineFail :: MimerStats -> MimerStats
incCompHit       stats = stats {statCompHit       = succ $ statCompHit stats}
incCompGen       stats = stats {statCompGen       = succ $ statCompGen stats}
incCompRegen     stats = stats {statCompRegen     = succ $ statCompRegen stats}
incCompNoRegen   stats = stats {statCompNoRegen   = succ $ statCompNoRegen stats}
incMetasCreated  stats = stats {statMetasCreated  = succ $ statMetasCreated stats}
incTypeEqChecks  stats = stats {statTypeEqChecks  = succ $ statTypeEqChecks stats}
incRefineSuccess stats = stats {statRefineSuccess = succ $ statRefineSuccess stats}
incRefineFail    stats = stats {statRefineFail    = succ $ statRefineFail stats}

