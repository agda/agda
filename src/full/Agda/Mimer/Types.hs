
module Agda.Mimer.Types where

import Control.DeepSeq (NFData)
import Data.Function (on)
import Data.Map (Map)
import GHC.Generics (Generic)
import Data.IORef (IORef)

import Agda.Syntax.Abstract (Expr)
import Agda.Syntax.Abstract qualified as A
import Agda.Syntax.Common.Pretty qualified as P
import Agda.Syntax.Common.Pretty (Pretty)
import Agda.Syntax.Common (InteractionId, Nat)
import Agda.Syntax.Internal
import Agda.TypeChecking.Monad (TCState, CheckpointId, Open, TCEnv, openThing)
import Agda.TypeChecking.Pretty
import Agda.TypeChecking.Substitute (NoSubst(..))
import Agda.Interaction.Base (Rewrite(..))
import Agda.Utils.Tuple (mapSnd)
import Agda.Utils.Impossible

import Agda.Mimer.Options

------------------------------------------------------------------------
-- * Results
------------------------------------------------------------------------

data MimerResult
  = MimerExpr String -- ^ Returns 'String' rather than 'Expr' because the give action expects a string.
  | MimerClauses QName [A.Clause]
  | MimerList [(Int, String)]
  | MimerNoResult
  deriving (Generic)

instance NFData MimerResult

data SearchStepResult
  = ResultExpr Expr
  | ResultClauses [A.Clause]
  | OpenBranch SearchBranch
  | NoSolution
  deriving (Generic)

instance NFData SearchStepResult

------------------------------------------------------------------------
-- * Search branches
------------------------------------------------------------------------

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

addBranchGoals :: [Goal] -> SearchBranch -> SearchBranch
addBranchGoals goals branch = branch {sbGoals = goals ++ sbGoals branch}

data Goal = Goal
  { goalMeta :: MetaId
  }
  deriving (Generic)
instance NFData Goal

-- TODO: Is this a reasonable Eq instance?
instance Eq Goal where
  g1 == g2 = goalMeta g1 == goalMeta g2

-- | Take the first goal off a search branch.
--   Precondition: the set of goals is non-empty.
nextGoal :: SearchBranch -> (Goal, SearchBranch)
nextGoal branch =
  case sbGoals branch of
    [] -> __IMPOSSIBLE__
    goal : goals -> (goal, branch{ sbGoals = goals })

------------------------------------------------------------------------
-- * Components
------------------------------------------------------------------------

-- Map source component to generated components
type ComponentCache = Map Component (Maybe [Component])

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

mkComponent :: CompId -> [MetaId] -> Cost -> Maybe Name -> Nat -> Term -> Type -> Component
mkComponent cId metaIds cost mName pars term typ = Component
  { compId    = cId
  , compName  = mName
  , compPars  = pars
  , compTerm  = term
  , compType  = typ
  , compRec   = False
  , compMetas = metaIds
  , compCost  = cost }

mkComponentQ :: CompId -> Cost -> QName -> Nat -> Term -> Type -> Component
mkComponentQ cId cost qname = mkComponent cId [] cost (Just $ qnameName qname)

noName :: Maybe Name
noName = Nothing

addCost :: Cost -> Component -> Component
addCost cost comp = comp { compCost = cost + compCost comp }

------------------------------------------------------------------------
-- * SearchOptions
------------------------------------------------------------------------

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

------------------------------------------------------------------------
-- * Measure performance
------------------------------------------------------------------------

data MimerStats = MimerStats
  { statCompHit       :: Nat -- ^ Could make use of an already generated component
  , statCompGen       :: Nat -- ^ Could use a generator for a component
  , statCompRegen     :: Nat -- ^ Had to regenerate the cache (new context)
  , statCompNoRegen   :: Nat -- ^ Did not have to regenerate the cache
  , statMetasCreated  :: Nat -- ^ Total number of meta-variables created explicitly (not through unification)
  , statTypeEqChecks  :: Nat -- ^ Number of times type equality is tested (with unification)
  , statRefineSuccess :: Nat -- ^ Number of times a refinement has been successful
  , statRefineFail    :: Nat -- ^ Number of times a refinement has failed
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

------------------------------------------------------------------------
-- * Pretty printing
------------------------------------------------------------------------

haskellRecord :: Doc -> [(Doc, Doc)] -> Doc
haskellRecord name fields = P.sep [ name, P.nest 2 $ P.braces (P.sep $ P.punctuate "," [ P.hang (k P.<+> "=") 2 v | (k, v) <- fields ]) ]

keyValueList :: [(Doc, Doc)] -> Doc
keyValueList kvs = P.braces $ P.sep $ P.punctuate "," [ P.hang (k P.<> ":") 2 v | (k, v) <- kvs ]

instance Pretty Goal where
  pretty goal = P.pretty $ goalMeta goal

instance Pretty SearchBranch where
  pretty branch = keyValueList
    [ ("sbTCState", "[...]")
    , ("sbGoals", P.pretty $ sbGoals branch)
    , ("sbCost", P.pretty $ sbCost branch)
    , ("sbComponentsUsed", P.pretty $ sbComponentsUsed branch)
    ]

instance PrettyTCM BaseComponents where
  prettyTCM comps = do
    let thisFn = case hintThisFn comps of
          Nothing -> "(nothing)"
          Just comp -> prettyComp comp
    vcat [ "Base components:"
         , nest 2 $ vcat
           [ f "hintFns" (hintFns comps)
           , f "hintDataTypes" (hintDataTypes comps)
           , f "hintRecordTypes" (hintRecordTypes comps)
           , f "hintAxioms" (hintAxioms comps)
           , f "hintLevel" (hintLevel comps)
           , f "hintProjections" (hintProjections comps)
           , "hintThisFn:" <+> thisFn
           , g prettyOpenComp "hintLetVars" (hintLetVars comps)
           , "hintRecVars: Open" <+> pretty (mapSnd unNoSubst <$> openThing (hintRecVars comps))
           ]
         ]
    where
      prettyComp comp = pretty (compTerm comp) <+> ":" <+> pretty (compType comp)
      prettyOpenComp openComp = "Open" <+> parens (prettyComp $ openThing openComp)
      prettyTCMComp comp = prettyTCM (compTerm comp) <+> ":" <+> prettyTCM (compType comp)
      f = g prettyTCMComp
      g p n [] = n <> ": []"
      g p n xs = (n <> ":") $+$ nest 2 (vcat $ map p xs)

instance Pretty BaseComponents where
  pretty comps = P.vcat
      [ f "hintFns" (hintFns comps)
      , f "hintDataTypes" (hintDataTypes comps)
      , f "hintRecordTypes" (hintRecordTypes comps)
      , f "hintAxioms" (hintAxioms comps)
      , f "hintLevel" (hintLevel comps)
      , f "hintProjections" (hintProjections comps)
      ]
    where
      f n [] = n P.<> ": []"
      f n xs = (n P.<> ":") P.$$ P.nest 2 (P.pretty xs)

instance Pretty SearchOptions where
  pretty opts = P.vcat
    [ "searchBaseComponents:"
    , P.nest 2 $ P.pretty $ searchBaseComponents opts
    , keyValueList
      [ ("searchHintMode", P.pretty $ searchHintMode opts)
      , ("searchTimeout",  P.pretty $ searchTimeout opts)
      , ("searchTopMeta",  P.pretty $ searchTopMeta opts)
      , ("searchTopEnv", "[...]")
      ]
    , "searchCosts:"
    , P.nest 2 (P.pretty $ searchCosts opts)
    ]

instance PrettyTCM SearchOptions where
  prettyTCM opts = vcat
    [ "searchBaseComponents:"
    , nest 2 $ prettyTCM $ searchBaseComponents opts
    , vcat
      [ "searchHintMode:" <+> pretty (searchHintMode opts)
      , "searchTimeout:" <+> pretty (searchTimeout opts)
      , "searchTopMeta:" <+> prettyTCM (searchTopMeta opts)
      , "searchTopEnv: [...]"
      , "searchTopCheckpoint:" <+> prettyTCM (searchTopCheckpoint opts)
      , "searchInteractionId:" <+> pretty (searchInteractionId opts)
      , "searchFnName:" <+> pretty (searchFnName opts)
      , "searchStats: [...]"
      ]
    , "searchCosts:"
    , nest 2 $ pretty $ searchCosts opts
    ]

instance Pretty Component where
  pretty comp = haskellRecord "Component"
    [ ("compId", P.pretty $ compId comp)
    , ("compTerm", P.pretty $ compTerm comp)
    , ("compType", P.pretty $ compType comp)
    , ("compMetas", P.pretty $ compMetas comp)
    , ("compCost", P.pretty $ compCost comp)
    ]

instance Pretty Costs where
  pretty costs = P.align 20 entries
    where
      entries =
        [ ("costLocal:"         , P.pretty $ costLocal costs)
        , ("costFn:"            , P.pretty $ costFn costs)
        , ("costDataCon:"       , P.pretty $ costDataCon costs)
        , ("costRecordCon:"     , P.pretty $ costRecordCon costs)
        , ("costSpeculateProj:" , P.pretty $ costSpeculateProj costs)
        , ("costProj:"          , P.pretty $ costProj costs)
        , ("costAxiom:"         , P.pretty $ costAxiom costs)
        , ("costLet:"           , P.pretty $ costLet costs)
        , ("costLevel:"         , P.pretty $ costLevel costs)
        , ("costSet:"           , P.pretty $ costSet costs)
        , ("costRecCall:"       , P.pretty $ costRecCall costs)
        , ("costNewMeta:"       , P.pretty $ costNewMeta costs)
        , ("costNewHiddenMeta:" , P.pretty $ costNewHiddenMeta costs)
        , ("costCompReuse:"     , "{function}")
        ]

instance PrettyTCM Component where
  prettyTCM Component{..} = parens (prettyTCM compId) <+> sep
    [ sep [ prettyTCM compTerm
          , ":" <+> prettyTCM compType ]
    , parens $ fsep $ punctuate ","
      [ "cost:" <+> prettyTCM compCost
      , "metas:" <+> prettyTCM compMetas
      ]
    ]

instance PrettyTCM MimerResult where
  prettyTCM = \case
    MimerExpr expr    -> pretty expr
    MimerClauses f cl -> "MimerClauses" <+> pretty f <+> "[..]" -- TODO: display the clauses
    MimerNoResult     -> "MimerNoResult"
    MimerList sols    -> "MimerList" <+> pretty sols

