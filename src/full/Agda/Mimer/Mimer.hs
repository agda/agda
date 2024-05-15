module Agda.Mimer.Mimer
  ( MimerResult(..)
  , mimer
  )
  where

import Control.DeepSeq (force, NFData(..))
import Control.Monad
import Control.Monad.Except (catchError)
import Control.Monad.Error.Class (MonadError)
import Control.Monad.Fail (MonadFail)
import Control.Monad.IO.Class (liftIO)
import Control.Monad.Reader (ReaderT(..), runReaderT, asks, ask, lift)
import Data.Function (on)
import Data.Functor ((<&>))
import Data.List (sortOn, intersect, transpose, (\\))
import qualified Data.List.NonEmpty as NonEmptyList (head)
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Maybe (maybeToList, fromMaybe, maybe, isNothing)
import Data.PQueue.Min (MinQueue)
import qualified Data.PQueue.Min as Q
import GHC.Generics (Generic)
import qualified Text.PrettyPrint.Boxes as Box
import qualified Data.Text as Text

import qualified Agda.Benchmarking as Bench
import Agda.Interaction.MakeCase (makeCase, getClauseZipperForIP, recheckAbstractClause)
import Agda.Syntax.Abstract (Expr(AbsurdLam))
import qualified Agda.Syntax.Abstract as A
import qualified Agda.Syntax.Abstract.Views as A
import Agda.Syntax.Abstract.Name (QName(..), Name(..))
import Agda.Syntax.Common (InteractionId(..), MetaId(..), ArgInfo(..), defaultArgInfo, Origin(..), ConOrigin(..), Hiding(..), setOrigin, NameId, Nat, namedThing, Arg(..), setHiding, getHiding, ProjOrigin(..), rangedThing, woThing, nameOf, visible)
import Agda.Syntax.Common.Pretty (Pretty)
import qualified Agda.Syntax.Common.Pretty as P
import qualified Agda.Syntax.Concrete.Name as C
import Agda.Syntax.Info (pattern UnificationMeta, exprNoRange)
import Agda.Syntax.Internal
import Agda.Syntax.Internal.MetaVars (AllMetas(..))
import Agda.Syntax.Internal.Pattern (clausePerm)
import Agda.Syntax.Position (Range, rangeFile, rangeFilePath)
import qualified Agda.Syntax.Scope.Base as Scope
import Agda.Syntax.Translation.InternalToAbstract (reify, NamedClause(..))
import Agda.Syntax.Translation.AbstractToConcrete (abstractToConcrete_)
import Agda.TypeChecking.Constraints (noConstraints)
import Agda.TypeChecking.Conversion (equalType)
import qualified Agda.TypeChecking.Empty as Empty -- (isEmptyType)
import Agda.TypeChecking.Free (flexRigOccurrenceIn, freeVars)
import Agda.TypeChecking.Level (levelType)
import Agda.TypeChecking.MetaVars (newValueMeta)
import Agda.TypeChecking.Monad -- (MonadTCM, lookupInteractionId, getConstInfo, liftTCM, clScope, getMetaInfo, lookupMeta, MetaVariable(..), metaType, typeOfConst, getMetaType, MetaInfo(..), getMetaTypeInContext)
import Agda.TypeChecking.Pretty
import Agda.TypeChecking.Records (isRecord, isRecursiveRecord)
import Agda.TypeChecking.Reduce (reduce, instantiateFull, instantiate)
import Agda.TypeChecking.Rules.LHS.Problem (AsBinding(..))
import Agda.TypeChecking.Rules.Term  (lambdaAddContext)
import Agda.TypeChecking.Substitute.Class (apply, applyE, NoSubst(..))
import Agda.TypeChecking.Telescope (piApplyM, flattenTel, teleArgs)
import Agda.Utils.Benchmark (billTo)
import Agda.Utils.FileName (filePath)
import Agda.Utils.Impossible (__IMPOSSIBLE__)
import Agda.Utils.Maybe (catMaybes)
import Agda.Utils.Monad (ifM)
import qualified Agda.Utils.Maybe.Strict as SMaybe
-- import Agda.Utils.Permutation (idP, permute, takeP)
import Agda.Utils.Time (CPUTime(..), getCPUTime, fromMilliseconds)
import Agda.Utils.Tuple (mapFst, mapSnd)
import Agda.Utils.FileName (AbsolutePath(..))

import Agda.Mimer.Options

import System.IO.Unsafe (unsafePerformIO)
import Data.IORef (IORef, writeIORef, readIORef, newIORef, modifyIORef')

-- Temporary (used for custom cost verbosity hack)
import qualified Agda.Utils.Maybe.Strict as Strict
import qualified Agda.Utils.Trie as Trie
import Agda.Interaction.Options.Base (parseVerboseKey)
import Agda.Utils.List (lastWithDefault)

data MimerResult
  = MimerExpr String -- ^ Returns 'String' rather than 'Expr' because the give action expects a string.
  | MimerClauses QName [A.Clause]
  | MimerList [(Int, String)]
  | MimerNoResult
  deriving (Generic)

instance NFData MimerResult

mimer :: MonadTCM tcm
  => InteractionId
  -> Range
  -> String
  -> tcm MimerResult
mimer ii rng argStr = liftTCM $ do
    reportSDoc "mimer.top" 10 ("Running Mimer on interaction point" <+> pretty ii <+> "with argument string" <+> text (show argStr))

    start <- liftIO $ getCPUTime

    opts <- parseOptions ii rng argStr
    reportS "mimer.top" 15 ("Mimer options: " ++ show opts)

    oldState <- getTC

    sols <- runSearch opts ii rng
    putTC oldState

    sol <- case drop (optSkip opts) $ zip [0..] sols of
          [] -> do
            reportSLn "mimer.top" 10 "No solution found"
            return MimerNoResult
          sols' | optList opts -> pure $ MimerList [ (i, s) | (i, MimerExpr s) <- sols' ]
          (_, sol) : _ -> do
            reportSDoc "mimer.top" 10 $ "Solution:" <+> prettyTCM sol
            return sol

    putTC oldState

    stop <- liftIO $ getCPUTime
    let time = stop - start
    reportSDoc "mimer.top" 10 ("Total elapsed time:" <+> pretty time)
    verboseS "mimer.stats" 50 $ writeTime ii (if null sols then Nothing else Just time)
    return sol


-- Order to try things in:
-- 1. Local variables (including let-bound)
-- 2. Data constructors
-- 3. Where clauses
-- 4. Lambda abstract
-- Other: Equality, empty type, record projections
-- - If we only use constructors if the target type is a data type, we might
--   generate η-reducible expressions, e.g. λ xs → _∷_ 0 xs


------------------------------------------------------------------------------
-- * Data types
------------------------------------------------------------------------------

type SM a = ReaderT SearchOptions TCM a

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
-- * Helper functions
------------------------------------------------------------------------------

predNat :: Nat -> Nat
predNat n | n > 0 = n - 1
          | n == 0 = 0
          | otherwise = error "predNat of negative value"

getRecordFields :: (HasConstInfo tcm, MonadTCM tcm) => QName -> tcm [QName]
getRecordFields = fmap (map unDom . recFields . theDef) . getConstInfo


-- TODO: Change the signature in original module instead.
isEmptyType :: Type -> SM Bool
isEmptyType = liftTCM . Empty.isEmptyType

-- TODO: Currently not using this function. Is it useful anywhere?
getDomainType :: Type -> Type
getDomainType typ = case unEl typ of
  Pi dom _ -> unDom dom
  _ -> __IMPOSSIBLE__

allOpenMetas :: (AllMetas t, ReadTCState tcm) => t -> tcm [MetaId]
allOpenMetas t = do
  openMetas <- getOpenMetas
  return $ allMetas (:[]) t `intersect` openMetas

getOpenComponent :: MonadTCM tcm => Open Component -> tcm Component
getOpenComponent openComp = do
  let comp = openThing openComp
  term <- getOpen $ compTerm <$> openComp
  typ <- getOpen $ compType <$> openComp
  when (not $ null $ compMetas comp) __IMPOSSIBLE__
  return Component
    { compId    = compId comp
    , compName  = compName comp
    , compPars  = compPars comp
    , compTerm  = term
    , compType  = typ
    , compRec   = compRec comp
    , compMetas = compMetas comp
    , compCost  = compCost comp
    }

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

newComponent :: MonadFresh CompId m => [MetaId] -> Cost -> Maybe Name -> Nat -> Term -> Type -> m Component
newComponent metaIds cost mName pars term typ = fresh <&> \cId -> mkComponent cId metaIds cost mName pars term typ

newComponentQ :: MonadFresh CompId m => [MetaId] -> Cost -> QName -> Nat -> Term -> Type -> m Component
newComponentQ metaIds cost qname pars term typ = fresh <&> \cId -> mkComponent cId metaIds cost (Just $ qnameName qname) pars term typ

addCost :: Cost -> Component -> Component
addCost cost comp = comp { compCost = cost + compCost comp }

addBranchGoals :: [Goal] -> SearchBranch -> SearchBranch
addBranchGoals goals branch = branch {sbGoals = goals ++ sbGoals branch}

withBranchState :: SearchBranch -> SM a -> SM a
withBranchState br ma = do
  putTC (sbTCState br)
  ma

withBranchAndGoal :: SearchBranch -> Goal -> SM a -> SM a
withBranchAndGoal br goal ma = inGoalEnv goal $ withBranchState br ma

inGoalEnv :: Goal -> SM a -> SM a
inGoalEnv goal = withMetaId (goalMeta goal)

nextBranchMeta' :: SearchBranch -> SM (Goal, SearchBranch)
nextBranchMeta' = fmap (fromMaybe __IMPOSSIBLE__) . nextBranchMeta

nextBranchMeta :: SearchBranch -> SM (Maybe (Goal, SearchBranch))
nextBranchMeta branch = case sbGoals branch of
  [] -> return Nothing
  (goal : goals) ->
    return $ Just (goal, branch{sbGoals=goals})

-- TODO: Rename (see metaInstantiation)
getMetaInstantiation :: (MonadTCM tcm, PureTCM tcm, MonadDebug tcm, MonadInteractionPoints tcm, MonadFresh NameId tcm)
  => MetaId -> tcm (Maybe Expr)
getMetaInstantiation = metaInstantiation >=> go
  where
    -- TODO: Cleaner way of juggling the maybes here?
    go Nothing = return Nothing
    go (Just term) = do
      expr <- instantiateFull term >>= reify
      return $ Just expr

metaInstantiation :: (MonadTCM tcm, MonadDebug tcm, ReadTCState tcm) => MetaId -> tcm (Maybe Term)
metaInstantiation metaId = lookupLocalMeta metaId <&> mvInstantiation >>= \case
  InstV inst -> return $ Just $ instBody inst
  _ -> return Nothing

isTypeDatatype :: (MonadTCM tcm, MonadReduce tcm, HasConstInfo tcm) => Type -> tcm Bool
isTypeDatatype typ = do
  typ' <- reduce typ
  case unEl typ' of
    Def qname _ -> theDef <$> getConstInfo qname >>= \case
      Datatype{} -> return True
      _ -> return False
    _ -> return False

------------------------------------------------------------------------------
-- * Components
------------------------------------------------------------------------------

-- ^ NOTE: Collects components from the *current* context, not the context of
-- the 'InteractionId'.
collectComponents :: Options -> Costs -> InteractionId -> Maybe QName -> [QName] -> MetaId -> TCM BaseComponents
collectComponents opts costs ii mDefName whereNames metaId = do
  lhsVars' <- collectLHSVars ii
  let recVars = lhsVars' <&> \ vars -> [ (tm, NoSubst i) | (tm, Just i) <- vars ]
  lhsVars <- getOpen $ map fst <$> lhsVars'
  typedLocals <- getLocalVarTerms 0
  reportSDoc "mimer.components" 40 $ "All LHS variables:" <+> prettyTCM lhsVars <+> parens ("or" <+> pretty lhsVars)
  let typedLhsVars = filter (\(term,typ) -> term `elem` lhsVars) typedLocals
  reportSDoc "mimer.components" 40 $
    "LHS variables with types:" <+> prettyList (map prettyTCMTypedTerm typedLhsVars) <+> parens ("or"
      <+> prettyList (map prettyTypedTerm typedLhsVars))
  -- TODO: For now, we *never* split on implicit arguments even if they are
  -- written explicitly on the LHS.
  splitVarsTyped <- filterM (\(term, typ) ->
                 ((argInfoHiding (domInfo typ) == NotHidden) &&) <$> isTypeDatatype (unDom typ))
               typedLhsVars
  reportSDoc "mimer.components" 40 $
    "Splittable variables" <+> prettyList (map prettyTCMTypedTerm splitVarsTyped) <+> parens ("or"
      <+> prettyList (map prettyTypedTerm splitVarsTyped))

  splitVars <- makeOpen $ map fst splitVarsTyped

  letVars <- getLetVars (costLet costs)


  let components = BaseComponents
        { hintFns = []
        , hintDataTypes = []
        , hintRecordTypes = []
        , hintProjections = []
        , hintAxioms = []
        , hintLevel = []
        , hintThisFn = Nothing
        , hintRecVars = recVars
        , hintLetVars = letVars
        , hintSplitVars = splitVars
        }
  metaVar <- lookupLocalMeta metaId
  hintNames <- getEverythingInScope metaVar
  components' <- foldM go components $ explicitHints ++ (hintNames \\ explicitHints)
  return BaseComponents
    { hintFns = doSort $ hintFns components'
    , hintDataTypes = doSort $ hintDataTypes components'
    , hintRecordTypes = doSort $ hintRecordTypes components'
    , hintProjections = doSort $ hintProjections components'
    , hintAxioms = doSort $ hintAxioms components'
    , hintLevel = doSort $ hintLevel components'
    , hintThisFn = hintThisFn components'
    , hintRecVars = recVars
    , hintLetVars = letVars
    , hintSplitVars = splitVars
    }
  where
    hintMode = optHintMode opts
    explicitHints = optExplicitHints opts
    -- Sort by the arity of the type
    doSort = sortOn (arity . compType)

    isNotMutual qname f = case mDefName of
      Nothing -> True
      Just defName -> defName /= qname && fmap ((defName `elem`)) (funMutual f) /= Just True

    go comps qname = do
      info <- getConstInfo qname
      typ <- typeOfConst qname
      scope <- getScope
      let addLevel  = qnameToComponent (costLevel   costs) qname <&> \ comp -> comps{hintLevel     = comp : hintLevel  comps}
          addAxiom  = qnameToComponent (costAxiom   costs) qname <&> \ comp -> comps{hintAxioms    = comp : hintAxioms comps}
          addThisFn = qnameToComponent (costRecCall costs) qname <&> \ comp -> comps{hintThisFn    = Just comp{ compRec = True }}
          addFn     = qnameToComponent (costFn      costs) qname <&> \ comp -> comps{hintFns       = comp : hintFns comps}
          addData   = qnameToComponent (costSet     costs) qname <&> \ comp -> comps{hintDataTypes = comp : hintDataTypes comps}
      case theDef info of
        Axiom{} | isToLevel typ    -> addLevel
                | shouldKeep scope -> addAxiom
                | otherwise        -> return comps
        -- TODO: Check if we want to use these
        DataOrRecSig{}   -> return comps
        GeneralizableVar -> return comps
        AbstractDefn{}   -> return comps
        -- If the function is in the same mutual block, do not include it.
        f@Function{}
          | Just qname == mDefName                  -> addThisFn
          | isToLevel typ && isNotMutual qname f    -> addLevel
          | isNotMutual qname f && shouldKeep scope -> addFn
          | otherwise                               -> return comps
        Datatype{} -> addData
        Record{} -> do
          projections <- mapM (qnameToComponent (costSpeculateProj costs)) =<< getRecordFields qname
          comp <- qnameToComponent (costSet costs) qname
          return comps{ hintRecordTypes = comp : hintRecordTypes comps
                      , hintProjections = projections ++ hintProjections comps }
        -- We look up constructors when we need them
        Constructor{} -> return comps
        -- TODO: special treatment for primitives?
        Primitive{} | isToLevel typ    -> addLevel
                    | shouldKeep scope -> addFn
                    | otherwise        -> return comps
        PrimitiveSort{} -> return comps
      where
        shouldKeep scope = or
          [ qname `elem` explicitHints
          , qname `elem` whereNames
          , case hintMode of
              Unqualified -> Scope.isNameInScopeUnqualified qname scope
              AllModules  -> True
              Module      -> Just (qnameModule qname) == mThisModule
              NoHints     -> False
          ]

        -- TODO: There is probably a better way of finding the module name
        mThisModule = qnameModule <$> mDefName

    -- NOTE: We do not reduce the type before checking, so some user definitions
    -- will not be included here.
    isToLevel :: Type -> Bool
    isToLevel typ = case unEl typ of
      Pi _ abs -> isToLevel (unAbs abs)
      Def qname _ -> P.prettyShow qname == builtinLevelName
      _ -> False

    prettyTCMTypedTerm :: (PrettyTCM tm, PrettyTCM ty) => (tm, ty) -> TCM Doc
    prettyTCMTypedTerm (term, typ) = prettyTCM term <+> ":" <+> prettyTCM typ
    prettyTypedTerm (term, typ) = pretty term <+> ":" <+> pretty typ

qnameToComponent :: (HasConstInfo tcm, ReadTCState tcm, MonadFresh CompId tcm, MonadTCM tcm)
  => Cost -> QName -> tcm Component
qnameToComponent cost qname = do
  info <- getConstInfo qname
  typ  <- typeOfConst qname
  -- #7120: typeOfConst is the type inside the module, so we need to apply the module params here
  mParams <- freeVarsToApply qname
  let def = (Def qname [] `apply` mParams, 0)
      (term, pars) = case theDef info of
        c@Constructor{}  -> (Con (conSrcCon c) ConOCon [], conPars c - length mParams)
        Axiom{}          -> def
        GeneralizableVar -> def
        Function{}       -> def
        Datatype{}       -> def
        Record{}         -> def
        Primitive{}      -> def
        PrimitiveSort{}  -> def
        DataOrRecSig{}   -> __IMPOSSIBLE__
        AbstractDefn{}   -> __IMPOSSIBLE__
  newComponentQ [] cost qname pars term typ

getEverythingInScope :: MonadTCM tcm => MetaVariable -> tcm [QName]
getEverythingInScope metaVar = do
  let scope = clScope $ getMetaInfo metaVar
  let nameSpace = Scope.everythingInScope scope
      names = Scope.nsNames nameSpace
      validKind = \ case
        Scope.PatternSynName           -> False   -- could consider allowing pattern synonyms, but the problem is they can't be getConstInfo'd
        Scope.GeneralizeName           -> False   -- and any way finding the underlying constructors should be easy
        Scope.DisallowedGeneralizeName -> False
        Scope.MacroName                -> False
        Scope.QuotableName             -> False
        Scope.ConName                  -> True
        Scope.CoConName                -> True
        Scope.FldName                  -> True
        Scope.DataName                 -> True
        Scope.RecName                  -> True
        Scope.FunName                  -> True
        Scope.AxiomName                -> True
        Scope.PrimName                 -> True
        Scope.OtherDefName             -> True
      qnames = map Scope.anameName
             . filter (validKind . Scope.anameKind)
             . map NonEmptyList.head
             $ Map.elems names
  return qnames

getLetVars :: (MonadFresh CompId tcm, MonadTCM tcm, Monad tcm) => Cost -> tcm [Open Component]
getLetVars cost = do
  bindings <- asksTC envLetBindings
  mapM makeComp $ Map.toAscList bindings
  where
    -- makeComp :: (Name, Open LetBinding) -> tcm (Open Component)
    makeComp (name, opn) = do
      cId <- fresh
      return $ opn <&> \ (LetBinding _ term typ) ->
                mkComponent cId [] cost (Just name) 0 term (unDom typ)

builtinLevelName :: String
builtinLevelName = "Agda.Primitive.Level"

-- IDEA:
-- [x] 1. Modify the collectRecVarCandidates to get all variables.
-- [ ] 2. Go through all variables to see if they are data types (not records)
-- [ ] 3. Run makeCase for those variables.
-- [ ] 4. Find out how to get the new interaction points/metas from the cases
-- [ ] 5. After search is done, compute out-of-scope variables.
-- [ ] 6. Run make-case again to introduce those variables.
-- [ ] 7. Redo the reification in the new clauses.
-- [ ] 8. Return the new clauses and follow Auto for insertion.

-- | Returns the variables as terms together with whether they where found under
-- some constructor, and if so which argument of the function they appeared in. This
-- information is used when building recursive calls, where it's important that we don't try to
-- construct non-terminating solutions.
collectLHSVars :: (MonadFail tcm, ReadTCState tcm, MonadError TCErr tcm, MonadTCM tcm, HasConstInfo tcm)
  => InteractionId -> tcm (Open [(Term, Maybe Int)])
collectLHSVars ii = do
  ipc <- ipClause <$> lookupInteractionPoint ii
  case ipc of
    IPNoClause -> makeOpen []
    IPClause{ipcQName = fnName, ipcClauseNo = clauseNr} -> do
      info <- getConstInfo fnName
      typ <- typeOfConst fnName
      parCount <- liftTCM getCurrentModuleFreeVars
      case theDef info of
        fnDef@Function{} -> do
          let clause = funClauses fnDef !! clauseNr
              naps = namedClausePats clause

          -- Telescope at interaction point
          iTel <- getContextTelescope
          -- Telescope for the body of the clause
          let cTel = clauseTel clause
          -- HACK: To get the correct indices, we shift by the difference in telescope lengths
          -- TODO: Difference between teleArgs and telToArgs?
          let shift = length (telToArgs iTel) - length (telToArgs cTel)

          reportSDoc "mimer" 60 $ vcat
            [ "Tel:"
            , nest 2 $ pretty iTel $$ prettyTCM iTel
            , "CTel:"
            , nest 2 $ pretty cTel $$ prettyTCM cTel
            ]
          reportSDoc "mimer" 60 $ "Shift:" <+> pretty shift

          makeOpen [ (Var (n + shift) [], (i - parCount) <$ guard underCon)    -- We count arguments excluding module parameters
                   | (i, nap) <- zip [0..] naps
                   , (n, underCon) <- go False $ namedThing $ unArg nap
                   ]
        _ -> do
          makeOpen []
  where
    go isUnderCon = \case
      VarP patInf x -> [(dbPatVarIndex x, isUnderCon)]
      DotP patInf t -> [] -- Ignore dot patterns
      ConP conHead conPatInf namedArgs -> concatMap (go True . namedThing . unArg) namedArgs
      LitP{} -> []
      ProjP{} -> []
      IApplyP{} -> [] -- Only for Cubical?
      DefP{} -> [] -- Only for Cubical?

declarationQnames :: A.Declaration -> [QName]
declarationQnames dec = [ q | Scope.WithKind _ q <- A.declaredNames dec ]

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

updateStat :: (MimerStats -> MimerStats) -> SM ()
updateStat f = verboseS "mimer.stats" 10 $ do
  ref <- asks searchStats
  liftIO $ modifyIORef' ref f


------------------------------------------------------------------------------
-- * Core algorithm
------------------------------------------------------------------------------

runSearch :: Options -> InteractionId -> Range -> TCM [MimerResult]
runSearch options ii rng = withInteractionId ii $ do
  (mTheFunctionQName, whereNames) <- fmap ipClause (lookupInteractionPoint ii) <&> \case
    clause@IPClause{} -> ( Just $ ipcQName clause
                         , case A.whereDecls $ A.clauseWhereDecls $ ipcClause clause of
                             Just decl -> declarationQnames decl
                             _ -> []
                         )
    IPNoClause -> (Nothing, [])

  reportSDoc "mimer.init" 15 $ "Interaction point in function:" <+> pretty mTheFunctionQName
  reportSDoc "mimer.init" 25 $ "Names in where-block" <+> pretty whereNames

  metaId <- lookupInteractionId ii
  metaVar <- lookupLocalMeta metaId

  -- We want to be able to solve with recursive calls
  setMetaOccursCheck metaId DontRunMetaOccursCheck

  metaIds <- case mvInstantiation metaVar of
    InstV inst -> do

      metaIds <- allOpenMetas (instBody inst)

      -- TODO: Make pretty instantiation for 'Instantiation'?
      reportSDoc "mimer.init" 20 $ sep [ "Interaction point already instantiated:" <+> pretty (instBody inst)
                                       , "with args" <+> pretty (instTel inst) ]

      -- ctx <- getContextTelescope
      return metaIds
    OpenMeta UnificationMeta -> do
      reportSLn "mimer.init" 20 "Interaction point not instantiated."
      return [metaId]
    _ -> __IMPOSSIBLE__
  -- TODO: Print each meta-variable's full context telescope
  reportSDoc "mimer.init" 20 $ "Remaining meta-variables to solve:" <+> prettyTCM metaIds
  reportSDoc "mimer.init" 20 $ "Meta var args" <+> (prettyTCM =<< getMetaContextArgs metaVar)


  fnArgs1 <- withShowAllArguments' False $ getContextArgs >>= mapM prettyTCM
  fnArgs2 <- withShowAllArguments' True  $ getContextArgs >>= mapM prettyTCM
  let bringScope = map snd $ filter (uncurry (/=)) $ zip fnArgs1 fnArgs2
      bringScopeNoBraces = map (filter (`notElem` ['{', '}']) . P.render) bringScope
  reportSDoc "mimer.temp" 20 $ vcat
    [ "Things to bring into scope:"
    , nest 2 $ vcat
      [ "Context args (don't show):" <+> pretty fnArgs1
      , "Context args (show all):  " <+> pretty fnArgs2
      , "To bring into scope:      " <+> pretty bringScope
      , "To bring into scope (str):" <+> pretty bringScopeNoBraces
      ]
    ]

  -- Check if there are any meta-variables to be solved
  case metaIds of
    -- No variables to solve, return the instantiation given
    [] -> do
      case mvInstantiation metaVar of
        InstV inst -> do
          expr <- withInteractionId ii $ do
            metaArgs <- getMetaContextArgs metaVar
            instantiateFull (apply (MetaV metaId []) metaArgs) >>= reify
          str <- P.render <$> prettyTCM expr
          let sol = MimerExpr str
          reportSDoc "mimer.init" 10 $ "Goal already solved. Solution:" <+> text str
          return [sol]
        _ -> __IMPOSSIBLE__
    _ -> do
      costs <- ifM (hasVerbosity "mimer.cost.custom" 10)
                 {- then -} customCosts
                 {- else -} (return defaultCosts)
      reportSDoc "mimer.cost.custom" 10 $ "Using costs:" $$ nest 2 (pretty costs)
      components <- collectComponents options costs ii mTheFunctionQName whereNames metaId
      let startGoals = map Goal metaIds

      state <- getTC
      env <- askTC

      let startBranch = SearchBranch
            { sbTCState = state
            , sbGoals = startGoals
            , sbCost = 0
            , sbCache = Map.empty
            , sbComponentsUsed = Map.empty
            }

      statsRef <- liftIO $ newIORef emptyMimerStats
      checkpoint <- viewTC eCurrentCheckpoint
      let searchOptions = SearchOptions
            { searchBaseComponents = components
            , searchHintMode = optHintMode options
            , searchTimeout = optTimeout options
            , searchGenProjectionsLocal = True
            , searchGenProjectionsLet = True
            , searchGenProjectionsExternal = False
            , searchGenProjectionsRec = True
            , searchSpeculateProjections = True
            , searchTopMeta = metaId
            , searchTopEnv = env
            , searchTopCheckpoint = checkpoint
            , searchInteractionId = ii
            , searchFnName = mTheFunctionQName
            , searchCosts = costs
            , searchStats = statsRef
            }

      reportSDoc "mimer.init" 20 $ "Using search options:" $$ nest 2 (prettyTCM searchOptions)
      reportSDoc "mimer.init" 20 $ "Initial search branch:" $$ nest 2 (pretty startBranch)

      flip runReaderT searchOptions $ bench [] $ do

        -- TODO: Check what timing stuff is used in Agda.Utils.Time
        timeout <- fromMilliseconds <$> asks searchTimeout
        startTime <- liftIO getCPUTime
        let go :: Int -> Int -> MinQueue SearchBranch -> SM ([MimerResult], Int)
            go 0 n _ = pure ([], n)
            go need n branchQueue = case Q.minView branchQueue of
              Nothing -> do
                reportSLn "mimer.search" 30 $ "No remaining search branches."
                return ([], n)
              Just (branch, branchQueue') -> do
                time <- liftIO getCPUTime
                mimerTrace 0 10 $ vcat
                  [ "Choosing branch"
                  , nest 2 $ sep
                    [ branchInstantiationDocCost branch <> ","
                    , nest 2 $ "metas:" <+> prettyTCM (map goalMeta $ sbGoals branch)
                    ]
                  ]
                reportSDoc "mimer.search" 50 $ "Full branch:" <+> pretty branch
                reportSMDoc "mimer.search" 50 $
                  "Instantiation of other branches:" <+> prettyList (map branchInstantiationDocCost $ Q.toAscList branchQueue')

                let elapsed = time - startTime
                if elapsed < timeout
                then do
                  (newBranches, sols) <- refine branch >>= partitionStepResult
                  let branchQueue'' = foldr Q.insert branchQueue' newBranches
                  reportSLn "mimer.search" 40 $ show (length sols) ++ " solutions found during cycle " ++ show (n + 1)
                  reportSMDoc "mimer.search" 45 $ "Solutions:" <+> prettyTCM sols
                  mimerTrace 0 40 $ vcat
                     [ "Cycle" <+> pretty (n + 1) <+> "branches"
                     , nest 2 $ vcat $ map branchInstantiationDocCost $ Q.toAscList branchQueue''
                     ]
                  unless (null sols) $ mimerTrace 0 20 $ vcat
                     [ "Cycle" <+> pretty (n + 1) <+> "solutions"
                     , nest 2 $ vcat $ map prettyTCM sols
                     ]

                  let sols' = take need sols
                  mapFst (sols' ++) <$> go (need - length sols') (n + 1) branchQueue''
                else do
                  reportSLn "mimer.search" 30 $ "Search time limit reached. Elapsed search time: " ++ show elapsed
                  return ([], n)
        let numSolutions | optList options = 10 + optSkip options
                         | otherwise       = 1 + optSkip options
        (sols, nrSteps) <- go numSolutions 0 $ Q.singleton startBranch
        reportSLn "mimer.search" 20 $ "Search ended after " ++ show (nrSteps + 1) ++ " cycles"
        -- results <- liftTCM $ mapM exprToStringAndVars sols
        reportSDoc "mimer.search" 15 $ "Solutions found: " <+> prettyList (map prettyTCM sols)
        reportSMDoc "mimer.stats" 10 $ do
          ref <- asks searchStats
          stats <- liftIO $ readIORef ref
          "Statistics:" <+> text (show stats)
        return sols

tryComponents :: Goal -> Type -> SearchBranch -> [(Component, [Component])] -> SM [SearchStepResult]
tryComponents goal goalType branch comps = withBranchAndGoal branch goal $ do
  checkpoint <- viewTC eCurrentCheckpoint
  let tryFor (sourceComp, comps') = do
        -- Clear out components that depend on meta-variables that have been used.
        let newCache = Map.insert sourceComp Nothing (sbCache branch Map.! checkpoint)
        newBranches <- catMaybes <$> mapM (tryRefineWith goal goalType branch) comps'
        return $ map (\br -> br{sbCache = Map.insert checkpoint newCache (sbCache branch)}) newBranches
  newBranches <- concatMapM tryFor comps
  mapM checkSolved newBranches

-- | If there is no cache entry for the checkpoint, create one. If there already
-- is one, even if the components are not yet generated for some entries, it is
-- returned as is.
prepareComponents :: Goal -> SearchBranch -> SM (SearchBranch, [(Component, [Component])])
prepareComponents goal branch = withBranchAndGoal branch goal $ do
  checkpoint <- viewTC eCurrentCheckpoint
  -- Check if we there is something in the cache for this checkpoint
  comps <- case Map.lookup checkpoint (sbCache branch) of
    -- No, generate components from scratch
    Nothing -> do
      updateStat incCompRegen
      reportSDoc "mimer.components" 20 $ vcat
        [ "No cache found checkpoint:" <+> pretty checkpoint
        , nest 2 $ "with context:" <+> (inTopContext . prettyTCM =<< getContextTelescope) ]
      -- Generate components for this context
      comps <- genComponents
      reportSDoc "mimer.components" 20 $ "Generated" <+> pretty (sum $ map (length . snd) comps) <+> "components"
      return comps
    -- Yes, just update the missing generated components
    Just cache -> mapM prepare (Map.toAscList cache)
  let newCache = Map.fromList $ map (mapSnd Just) comps
  branch' <- updateBranch [] branch{sbCache = Map.insert checkpoint newCache (sbCache branch)}
  return (branch', comps)
  where
  prepare :: (Component, Maybe [Component]) -> SM (Component, [Component])
  prepare (sourceComp, Just comps) = do
    updateStat incCompNoRegen
    return (sourceComp, comps)
  prepare (sourceComp, Nothing) = do
    updateStat incCompRegen
    (sourceComp,) <$> genComponentsFrom True sourceComp

localVarCount :: SM Int
localVarCount = do
  top <- asks $ length . envContext . searchTopEnv
  cur <- length <$> getContext
  pure $ cur - top

genComponents :: SM [(Component, [Component])]
genComponents = do
  opts <- ask
  let comps = searchBaseComponents opts
  n <- localVarCount
  localVars <- lift (getLocalVars n (costLocal $ searchCosts opts))
    >>= genAddSource (searchGenProjectionsLocal opts)
  recCalls <- genAddSource (searchGenProjectionsRec opts) (maybeToList $ hintThisFn comps)
  letVars <- mapM getOpenComponent (hintLetVars comps)
    >>= genAddSource (searchGenProjectionsLet opts)
  fns <- genAddSource (searchGenProjectionsExternal opts) (hintFns comps)
  axioms <- genAddSource (searchGenProjectionsExternal opts) (hintAxioms comps)
  return $ localVars ++ letVars ++ recCalls ++ fns ++ axioms
  where
    genAddSource :: Bool -> [Component] -> SM [(Component, [Component])]
    genAddSource genProj = mapM (\comp -> (comp,) <$> genComponentsFrom genProj comp)


genComponentsFrom :: Bool -- ^ Apply record elimination
                  -> Component
                  -> SM [Component]
genComponentsFrom appRecElims origComp = do
  comps <- if | compRec origComp -> mapM (applyToMetasG Nothing) =<< genRecCalls origComp
              | otherwise        -> (:[]) <$> applyToMetasG Nothing origComp
  if appRecElims
  then concat <$> mapM (applyProjections Set.empty) comps
  else return comps
  where
  applyProjections :: Set QName -> Component -> SM [Component]
  applyProjections seenRecords comp = do
    projComps <- getRecordInfo (compType comp) >>= \case
      Nothing -> return []
      Just (recordName, args, fields, isRecursive)
          | Set.member recordName seenRecords -> do
              reportSDoc "mimer.components" 60 $
                "Skipping projection because recursive record already seen:" <+> pretty recordName
              return []
          | otherwise -> do
              let seenRecords' = if isRecursive then Set.insert recordName seenRecords else seenRecords
              comps <- mapM (applyProj args comp >=> applyToMetasG Nothing) fields
              concatMapM (applyProjections seenRecords') comps
    return $ comp : projComps

getRecordInfo :: Type
  -> SM (Maybe ( QName     -- Record name
               , Args      -- Record parameters converted to (hidden) arguments
               , [QName]   -- Field names
               , Bool      -- Is recursive?
               ))
getRecordInfo typ = case unEl typ of
  Def qname elims -> isRecord qname >>= \case
    Nothing -> return Nothing
    Just defn -> do
      fields <- getRecordFields qname
      return $ Just (qname, argsFromElims elims, fields, recRecursive defn)
  _ -> return Nothing

applyProj :: Args -> Component -> QName -> SM Component
applyProj recordArgs comp' qname = do
  cost <- asks (costProj . searchCosts)
  let newTerm = applyE (compTerm comp') [Proj ProjSystem qname]
  projType <- defType <$> getConstInfo qname
  projTypeWithArgs <- piApplyM projType recordArgs
  newType <- piApplyM projTypeWithArgs (compTerm comp')
  newComponentQ (compMetas comp') (compCost comp' + cost) qname 0 newTerm newType


-- TODO: currently reducing twice
applyToMetasG
  :: Maybe Nat -- ^ Max number of arguments to apply.
  -> Component -> SM Component
applyToMetasG (Just m) comp | m <= 0 = return comp
applyToMetasG maxArgs comp = do
  ctx <- getContextTelescope
  compTyp <- reduce $ compType comp
  case unEl compTyp of
    Pi dom abs -> do
      let domainType = unDom dom
      (metaId, metaTerm) <- createMeta domainType
      let arg = setOrigin Inserted $ metaTerm <$ argFromDom dom
      newType <- reduce =<< piApplyM (compType comp) metaTerm
      -- Constructors the parameters are not included in the term
      let skip = compPars comp
          newTerm | skip > 0  = compTerm comp
                  | otherwise = apply (compTerm comp) [arg]
      cost <- asks $ (if getHiding arg == Hidden then costNewHiddenMeta else costNewMeta) . searchCosts
      applyToMetasG (predNat <$> maxArgs)
                    comp{ compTerm = newTerm
                        , compType = newType
                        , compPars = predNat skip
                        , compMetas = metaId : compMetas comp
                        , compCost = cost + compCost comp
                        }
    _ ->
      -- Set the type to the reduced version
      return comp{compType = compTyp}

createMeta :: Type -> SM (MetaId, Term)
createMeta typ = do
  (metaId, metaTerm) <- newValueMeta DontRunMetaOccursCheck CmpLeq typ
  verboseS "mimer.stats" 20 $ updateStat incMetasCreated
  reportSDoc "mimer.components" 80 $ do
    "Created meta-variable (type in context):" <+> pretty metaTerm <+> ":" <+> (pretty =<< getMetaTypeInContext metaId)
  return (metaId, metaTerm)


partitionStepResult :: [SearchStepResult] -> SM ([SearchBranch], [MimerResult])
partitionStepResult [] = return ([],[])
partitionStepResult (x:xs) = do
  let rest = partitionStepResult xs
  (brs',sols) <- rest
  case x of
    NoSolution -> rest
    OpenBranch br -> return (br:brs', sols)
    ResultExpr exp -> do
      str <- P.render <$> prettyTCM exp
      return $ (brs', MimerExpr str : sols)
    ResultClauses cls -> do
      f <- fromMaybe __IMPOSSIBLE__ <$> asks searchFnName
      return $ (brs', MimerClauses f cls : sols)


topInstantiationDoc :: SM Doc
topInstantiationDoc = asks searchTopMeta >>= getMetaInstantiation >>= maybe (return "(nothing)") prettyTCM

prettyGoalInst :: Goal -> SM Doc
prettyGoalInst goal = inGoalEnv goal $ do
  args <- map Apply <$> getContextArgs
  prettyTCM =<< instantiate (MetaV (goalMeta goal) args)

branchInstantiationDocCost :: SearchBranch -> SM Doc
branchInstantiationDocCost branch = branchInstantiationDoc branch <+> parens ("cost:" <+> pretty (sbCost branch))

-- | For debug
branchInstantiationDoc :: SearchBranch -> SM Doc
branchInstantiationDoc branch = withBranchState branch topInstantiationDoc

refine :: SearchBranch -> SM [SearchStepResult]
refine branch = withBranchState branch $ do
  (goal1, branch1) <- nextBranchMeta' branch

  withBranchAndGoal branch1 goal1 $ do
    goalType1 <- bench [Bench.Reduce] $ reduce =<< getMetaTypeInContext (goalMeta goal1)

    mimerTrace 1 10 $ sep
      [ "Refining goal"
      , nest 2 $ prettyTCM (goalMeta goal1) <+> ":" <+> prettyTCM goalType1
      , nest 2 $ "in context" <+> (inTopContext . prettyTCM =<< getContextTelescope)
      ]

    reportSDoc "mimer.refine" 30 $ "Goal type:" <+> pretty goalType1
    reportSDoc "mimer.refine" 30 $ "Goal context:" <+> (pretty =<< getContextTelescope)

    -- Lambda-abstract as far as possible
    tryLamAbs goal1 goalType1 branch1 >>= \case
      -- Abstracted with absurd pattern: solution found.
      Left expr -> do
        reportSDoc "mimer.refine" 30 $ "Abstracted with absurd lambda. Result:" <+> prettyTCM expr
        return [ResultExpr expr]
      -- Normal abstraction
      Right (goal2, goalType2, branch2) -> withBranchAndGoal branch2 goal2 $ do
        (branch3, components) <- prepareComponents goal2 branch2
        withBranchAndGoal branch3 goal2 $ do

          when (goalMeta goal2 /= goalMeta goal1) $ do
            mimerTrace 1 10 $ sep
              [ "Lambda refinement", nest 2 $ prettyGoalInst goal1 ]
            mimerTrace 1 10 $ sep
              [ "Refining goal"
              , nest 2 $ prettyTCM (goalMeta goal2) <+> ":" <+> prettyTCM goalType2
              , nest 2 $ "in context" <+> (inTopContext . prettyTCM =<< getContextTelescope)
              ]

          mimerTrace 2 40 $ vcat
            [ "Components:"
            , nest 2 $ vcat $ map prettyTCM $ concatMap snd components
            ]

          results1 <- tryComponents goal2 goalType2 branch3 components
          results2 <- tryDataRecord goal2 goalType2 branch3
          return $ results1 ++ results2

tryFns :: Goal -> Type -> SearchBranch -> SM [SearchStepResult]
tryFns goal goalType branch = withBranchAndGoal branch goal $ do
  reportSDoc "mimer.refine.fn" 50 $ "Trying functions"
  fns <- asks (hintFns . searchBaseComponents)
  newBranches <- catMaybes <$> mapM (tryRefineAddMetas goal goalType branch) fns
  mapM checkSolved newBranches

tryProjs :: Goal -> Type -> SearchBranch -> SM [SearchStepResult]
tryProjs goal goalType branch = withBranchAndGoal branch goal $ do
  projs <- asks (hintProjections . searchBaseComponents)
  newBranches <- catMaybes <$> mapM (tryRefineAddMetas goal goalType branch) projs
  mapM checkSolved newBranches

tryAxioms :: Goal -> Type -> SearchBranch -> SM [SearchStepResult]
tryAxioms goal goalType branch = withBranchAndGoal branch goal $ do
  axioms <- asks (hintAxioms . searchBaseComponents)
  newBranches <- catMaybes <$> mapM (tryRefineAddMetas goal goalType branch) axioms
  mapM checkSolved newBranches

tryLet :: Goal -> Type -> SearchBranch -> SM [SearchStepResult]
tryLet goal goalType branch = withBranchAndGoal branch goal $ do
  letVars <- asks (hintLetVars . searchBaseComponents) >>= mapM getOpenComponent
  newBranches <- catMaybes <$> mapM (tryRefineAddMetas goal goalType branch) letVars
  mapM checkSolved newBranches

-- | Returns @Right@ for normal lambda abstraction and @Left@ for absurd lambda.
tryLamAbs :: Goal -> Type -> SearchBranch -> SM (Either Expr (Goal, Type, SearchBranch))
tryLamAbs goal goalType branch =
  case unEl goalType of
    Pi dom abs -> do
     e <- isEmptyType (unDom dom)
     isEmptyType (unDom dom) >>= \case -- TODO: Is this the correct way of checking if absurd lambda is applicable?
      True -> do
        let argInf = defaultArgInfo{argInfoOrigin = Inserted} -- domInfo dom
            term = Lam argInf absurdBody
        newMetaIds <- assignMeta (goalMeta goal) term goalType
        unless (null newMetaIds) (__IMPOSSIBLE__)
        -- TODO: Represent absurd lambda as a Term instead of Expr.
        -- Left . fromMaybe __IMPOSSIBLE__ <$> getMetaInstantiation (goalMeta metaId)
        return $ Left $ AbsurdLam exprNoRange NotHidden
      False -> do
        let bindName | isNoName (absName abs) = "z"
                     | otherwise              = absName abs
        newName <- freshName_ bindName
        (metaId', bodyType, metaTerm, env) <- lambdaAddContext newName bindName dom $ do
          goalType' <- getMetaTypeInContext (goalMeta goal)
          bodyType <- bench [Bench.Reduce] $ reduce =<< piApplyM goalType' (Var 0 []) -- TODO: Good place to reduce?
          (metaId', metaTerm) <- bench [Bench.Free] $ newValueMeta DontRunMetaOccursCheck CmpLeq bodyType
          env <- askTC
          return (metaId', bodyType, metaTerm, env)

        let argInf = domInfo dom -- TODO: is this the correct arg info?
            newAbs = Abs{absName = bindName, unAbs = metaTerm } --MetaV metaId' [] }
            -- look at mkLam
            term = Lam argInf newAbs

        newMetaIds <- assignMeta (goalMeta goal) term goalType

        withEnv env $ do
          branch' <- updateBranch newMetaIds branch
          tryLamAbs (Goal metaId') bodyType branch'
    _ -> do
      branch' <- updateBranch [] branch -- TODO: Is this necessary?
      return $ Right (goal, goalType, branch')


genRecCalls :: Component -> SM [Component]
genRecCalls thisFn = do
  -- TODO: Make sure there are no pruning problems
  asks (hintRecVars . searchBaseComponents) >>= getOpen >>= \case
    -- No candidate arguments for a recursive call
    [] -> return []
    recCandTerms -> do
      Costs{..} <- asks searchCosts
      n <- localVarCount
      localVars <- lift $ getLocalVars n costLocal
      let recCands = [ (t, i) | t@(compTerm -> v@Var{}) <- localVars, NoSubst i <- maybeToList $ lookup v recCandTerms ]

      let newRecCall = do
            -- Apply the recursive call to new metas
            (thisFnTerm, thisFnType, newMetas) <- applyToMetas 0 (compTerm thisFn) (compType thisFn)
            let argGoals = map Goal newMetas
            comp <- newComponent newMetas (compCost thisFn) (compName thisFn) 0 thisFnTerm thisFnType
            return (comp, zip argGoals [0..])

          -- go :: Component -- ^ Recursive call function applied to meta-variables
          --   -> [(Goal, Int)] -- ^ Remaining parameters to try to fill
          --   -> [(Component, Int)] -- ^ Remaining argument candidates for the current parameter
          --   -> SM [Component]
          go _thisFn [] _args = return []
          go thisFn (_ : goals) [] = go thisFn goals recCands
          go thisFn ((goal, i) : goals) ((arg, j) : args) | i == j = do
            reportSMDoc "mimer.components.rec" 80 $ hsep
              [ "Trying to generate recursive call"
              , prettyTCM (compTerm thisFn)
              , "with" <+> prettyTCM (compTerm arg)
              , "for" <+> prettyTCM (goalMeta goal) ]
            goalType <- getMetaTypeInContext (goalMeta goal)
            state <- getTC
            tryRefineWith' goal goalType arg >>= \case
              Nothing -> do
                putTC state
                go thisFn ((goal, i) : goals) args
              Just (newMetas1, newMetas2) -> do
                let newComp = thisFn{compMetas = newMetas1 ++ newMetas2 ++ (compMetas thisFn \\ [goalMeta goal])}
                (thisFn', goals') <- newRecCall
                (newComp:) <$> go thisFn' (drop (length goals' - length goals - 1) goals') args
          go thisFn goals (_ : args) = go thisFn goals args
      (thisFn', argGoals) <- newRecCall
      comps <- go thisFn' argGoals recCands
      -- Compute costs for the calls:
      --  - costNewMeta/costNewHiddenMeta for each unsolved argument
      --  - zero for solved arguments
      --  - costLocal for the parameter we recurse on
      let callCost comp = (costLocal +) . sum <$> argCosts (compTerm comp)
          argCosts (Def _ elims) = mapM argCost elims
          argCosts _ = __IMPOSSIBLE__
          argCost (Apply arg) = instantiate arg <&> \ case
            Arg h MetaV{} | visible h -> costNewMeta
                          | otherwise -> costNewHiddenMeta
            _ -> 0
          argCost Proj{}   = pure 0
          argCost IApply{} = pure 0
      mapM (\ c -> (`addCost` c) <$> callCost c) comps


-- TODO: Factor out `checkSolved`
tryDataRecord :: Goal -> Type -> SearchBranch -> SM [SearchStepResult]
tryDataRecord goal goalType branch = withBranchAndGoal branch goal $ do
  -- TODO: There is a `isRecord` function, which performs a similar case
  -- analysis as here, but it does not work for data types.
  case unEl goalType of
    Def qname elims -> theDef <$> getConstInfo qname >>= \case
      recordDefn@Record{} -> do
        tryRecord recordDefn
      dataDefn@Datatype{} -> do
        tryData dataDefn
      primitive@Primitive{} -> do
        return []
      -- TODO: Better way of checking that type is Level
      d@Axiom{}
        | P.prettyShow qname == "Agda.Primitive.Level" -> do
            tryLevel
        | otherwise -> do
        return []
      d@DataOrRecSig{} -> do
        return []
      d@GeneralizableVar -> do
        return []
      d@AbstractDefn{} -> do
        return []
      d@Function{} -> do
        return []
      d@Constructor{} -> do
        return []
      d@PrimitiveSort{} -> do
        return []
    sort@(Sort (Type level)) -> do
      trySet level
    Sort sort -> do
      return []
    _ -> return []
  where
      -- TODO: Alternatively, the constructor can be accessed via `getRecordConstructor`
      -- TODO: There might be a neater way of applying the constructor to new metas
    tryRecord :: Defn -> SM [SearchStepResult]
    tryRecord recordDefn = do
      cost <- asks (costRecordCon . searchCosts) -- TODO: Use lenses for this?
      comp <- qnameToComponent cost $ conName $ recConHead recordDefn
      -- NOTE: at most 1
      newBranches <- maybeToList <$> tryRefineAddMetas goal goalType branch comp
      mapM checkSolved newBranches

    tryData :: Defn -> SM [SearchStepResult]
    tryData dataDefn = do
      cost <- asks (costDataCon . searchCosts)
      comps <- mapM (qnameToComponent cost) $ dataCons dataDefn
      newBranches <- mapM (tryRefineAddMetas goal goalType branch) comps
      -- TODO: Reduce overlap between e.g. tryLocals, this and tryRecord
      mapM checkSolved (catMaybes newBranches)

    tryLevel :: SM [SearchStepResult]
    tryLevel = do
      levelHints <- asks (hintLevel . searchBaseComponents)
      newBranches <- catMaybes <$> mapM (tryRefineAddMetas goal goalType branch) levelHints
      mapM checkSolved newBranches

    -- TODO: Add an extra filtering on the sort
    trySet :: Level -> SM [SearchStepResult]
    trySet level = do
      reducedLevel <- reduce level
      cost <- asks (costSet . searchCosts)
      setCandidates <- case reducedLevel of
        (Max i [])
          | i > 0 -> do
              comp <- newComponent [] cost Nothing 0 (Sort $ Type $ Max (i - 1) []) goalType
              return [(branch, comp)]
          | otherwise -> return []
        (Max i ps) -> do
              (metaId, metaTerm) <- createMeta =<< levelType
              comp <- newComponent [metaId] cost Nothing 0 (Sort $ Type $ Max (max 0 (i - 1)) [Plus 0 metaTerm]) goalType
              branch' <- updateBranch [metaId] branch
              return [(branch', comp)]
      reportSDoc "mimer.refine.set" 40 $
        "Trying" <+> prettyTCM (map snd setCandidates) <+> "for" <+> prettyTCM goalType
      newBranches <- catMaybes <$> mapM (\(br,c) -> tryRefineWith goal goalType br c) setCandidates
      components <- asks searchBaseComponents
      newBranches' <- catMaybes <$> mapM (tryRefineAddMetas goal goalType branch)
                      (concatMap ($ components)
                       [ hintDataTypes
                       , hintRecordTypes
                       , hintAxioms])
      mapM checkSolved (newBranches ++ newBranches')

-- | Type should already be reduced here
-- NOTE: Does not reset the state!
-- TODO: Make sure the type is always reduced
tryRefineWith :: Goal -> Type -> SearchBranch -> Component -> SM (Maybe SearchBranch)
tryRefineWith goal goalType branch comp = withBranchAndGoal branch goal $ do

  metasCreatedBy (dumbUnifierErr (compType comp) goalType) >>= \case
    (Nothing, newMetaStore) -> do
      updateStat incRefineSuccess
      -- TODO: Why is newMetaIds not used here?
      newMetaIds <- assignMeta (goalMeta goal) (compTerm comp) goalType
      let newMetaIds' = Map.keys (openMetas newMetaStore)
      reportSDoc "mimer.refine" 60 $
        "Refine: assignMeta created new metas:" <+> prettyTCM newMetaIds

      reportSMDoc "mimer.refine" 50 $ "Refinement succeeded"

      mimerTrace 2 10 $ sep
        [ "Found refinement"
        , nest 2 $ sep [ prettyTCM (compTerm comp)
                       , ":" <+> prettyTCM (compType comp) ] ]
      -- Take the metas stored in the component and add them as sub-goals
      Just <$> updateBranchCost comp (newMetaIds' ++ compMetas comp) branch
    (Just err, _) -> do
      updateStat incRefineFail
      reportSMDoc "mimer.refine" 50 $ "Refinement failed"

      mimerTrace 2 60 $ vcat
        [ "Failed refinement"
        , nest 2 $ sep [ prettyTCM (compTerm comp)
                       , ":" <+> prettyTCM (compType comp) ]
        , nest 2 $ prettyTCM err ]
      return Nothing

tryRefineWith' :: Goal -> Type -> Component -> SM (Maybe ([MetaId], [MetaId]))
tryRefineWith' goal goalType comp = do
  metasCreatedBy (dumbUnifier (compType comp) goalType) >>= \case
    (True, newMetaStore) -> do
      newMetaIds <- assignMeta (goalMeta goal) (compTerm comp) goalType
      let newMetaIds' = Map.keys (openMetas newMetaStore)
      return $ Just (newMetaIds, newMetaIds')
    (False, _) -> return Nothing

-- TODO: Make policy for when state should be put
tryRefineAddMetas :: Goal -> Type -> SearchBranch -> Component -> SM (Maybe SearchBranch)
tryRefineAddMetas goal goalType branch comp = withBranchAndGoal branch goal $ do
  -- Apply the hint to new metas (generating @c@, @c ?@, @c ? ?@, etc.)
  -- TODO: Where is the best place to reduce the hint type?
  comp' <- applyToMetasG Nothing comp
  branch' <- updateBranch [] branch
  tryRefineWith goal goalType branch' comp'

-- TODO: Make sure the type is reduced the first time this is called
-- TODO: Rewrite with Component?
-- NOTE: The new metas are in left-to-right order -- the opposite of the
-- order they should be solved in.
applyToMetas :: Nat -> Term -> Type -> SM (Term, Type, [MetaId])
applyToMetas skip term typ = do
  ctx <- getContextTelescope
  case unEl typ of
    Pi dom abs -> do
      let domainType = unDom dom
      -- TODO: What exactly does the occur check do?
      (metaId', metaTerm) <- bench [Bench.Free] $ newValueMeta DontRunMetaOccursCheck CmpLeq domainType
      let arg = setOrigin Inserted $ metaTerm <$ argFromDom dom
      newType <- bench [Bench.Reduce] $ reduce =<< piApplyM typ metaTerm -- TODO: Is this the best place to reduce?
      -- For records, the parameters are not included in the term
      let newTerm = if skip > 0 then term else apply term [arg]
      (term', typ', metas) <- applyToMetas (predNat skip) newTerm newType
      return (term', typ', metaId' : metas)
    _ -> return (term, typ, [])


checkSolved :: SearchBranch -> SM SearchStepResult
checkSolved branch = do
  topMetaId <- asks searchTopMeta
  topMeta <- lookupLocalMeta topMetaId
  ii <- asks searchInteractionId
  withInteractionId ii $ withBranchState branch $ do
    metaArgs <- getMetaContextArgs topMeta
    inst <- instantiateFull $ apply (MetaV topMetaId []) metaArgs
    case allMetas (:[]) inst of
      [] -> ResultExpr <$> reify inst
      metaIds -> do
        return $ OpenBranch $ branch{sbGoals = map Goal $ reverse metaIds}

setAt :: Int -> a -> [a] -> [a]
setAt i x xs = case splitAt i xs of
  (ls, _r:rs) -> ls ++ (x : rs)
  _ -> error "setAt: index out of bounds"

updateBranch' :: Maybe Component -> [MetaId] -> SearchBranch -> SM SearchBranch
updateBranch' mComp newMetaIds branch = do
  state <- getTC
  let compsUsed = sbComponentsUsed branch
  (deltaCost, compsUsed') <- case mComp of
        Nothing -> return (0, compsUsed)
        Just comp -> do
          case compName comp of
            Nothing -> return (compCost comp, compsUsed)
            Just name -> case compsUsed Map.!? name of
              Nothing -> return (compCost comp, Map.insert name 1 compsUsed)
              Just uses -> do
                reuseCost <- asks (costCompReuse . searchCosts)
                return (compCost comp + reuseCost uses, Map.adjust succ name compsUsed)
  return branch{ sbTCState = state
               , sbGoals = map Goal newMetaIds ++ sbGoals branch
               , sbCost = sbCost branch + deltaCost
               , sbComponentsUsed = compsUsed'
               }

updateBranch :: [MetaId] -> SearchBranch -> SM SearchBranch
updateBranch = updateBranch' Nothing

updateBranchCost :: Component -> [MetaId] -> SearchBranch -> SM SearchBranch
updateBranchCost comp = updateBranch' (Just comp)

assignMeta :: MetaId -> Term -> Type -> SM [MetaId]
assignMeta metaId term metaType = bench [Bench.CheckRHS] $ do
  ((), newMetaStore) <- metasCreatedBy $ do
    metaVar <- lookupLocalMeta metaId
    metaArgs <- getMetaContextArgs metaVar

    reportSMDoc "mimer.assignMeta" 60 $ vcat
      [ "Assigning" <+> pretty term
      , nest 2 $ vcat [ "to" <+> pretty metaId <+> ":" <+> pretty metaType
                      , "in context" <+> (pretty =<< getContextTelescope)
                      ]
      ]

    assignV DirLeq metaId metaArgs term (AsTermsOf metaType) `catchError` \err -> do
      reportSMDoc "mimer.assignMeta" 30 $ vcat
        [ "Got error from assignV:" <+> prettyTCM err
        , nest 2 $ vcat
          [ "when trying to assign" <+> prettyTCM term
          , "to" <+> prettyTCM metaId <+> ":" <+> prettyTCM metaType
          , "in context" <+> (inTopContext . prettyTCM =<< getContextTelescope)
          ]
        ]

  let newMetaIds = Map.keys (openMetas newMetaStore)
  return newMetaIds

dumbUnifier :: Type -> Type -> SM Bool
dumbUnifier t1 t2 = isNothing <$> dumbUnifierErr t1 t2

dumbUnifierErr :: Type -> Type -> SM (Maybe TCErr)
dumbUnifierErr t1 t2 = bench [Bench.UnifyIndices] $ do
  updateStat incTypeEqChecks
  noConstraints (Nothing <$ equalType t2 t1) `catchError` \err -> do
    reportSDoc "mimer.unify" 80 $ sep [ "Unification failed with error:", nest 2 $ prettyTCM err ]
    return $ Just err

-- Duplicate of a local definition in Agda.Interaction.BasicOps
showTCM :: (MonadPretty tcm, PrettyTCM a) => a -> tcm String
showTCM v = P.render <$> prettyTCM v

bench :: NFData a => [Bench.Phase] -> SM a -> SM a
bench k ma = billTo (mimerAccount : k) ma
  where
    -- Dummy account to avoid updating Bench. Doesn't matter since this is only used interactively
    -- to debug Mimer performance.
    mimerAccount = Bench.Sort

-- Local variables:
-- getContext :: MonadTCEnv m => m [Dom (Name, Type)]
-- getContextArgs :: (Applicative m, MonadTCEnv m) => m Args
-- getContextTelescope :: (Applicative m, MonadTCEnv m) => m Telescope
-- getContextTerms :: (Applicative m, MonadTCEnv m) => m [Term]
getLocalVars :: Int -> Cost -> TCM [Component]
getLocalVars localCxt cost = do
  typedTerms <- getLocalVarTerms localCxt
  let varZeroDiscount (Var 0 []) = 1
      varZeroDiscount _          = 0
  mapM (\(term, domTyp) -> newComponent [] (cost - varZeroDiscount term) noName 0 term (unDom domTyp)) typedTerms

getLocalVarTerms :: Int -> TCM [(Term, Dom Type)]
getLocalVarTerms localCxt = do
  contextTerms <- getContextTerms
  contextTypes <- flattenTel <$> getContextTelescope
  let inScope i _ | i < localCxt = pure True   -- Ignore scope for variables we inserted ourselves
      inScope _ Dom{ unDom = name } = do
        x <- abstractToConcrete_ name
        pure $ C.isInScope x == C.InScope
  scope <- mapM (uncurry inScope) =<< getContextVars
  return [ e | (True, e) <- zip scope $ zip contextTerms contextTypes ]



prettyBranch :: SearchBranch -> SM String
prettyBranch branch = withBranchState branch $ do
    metaId <- asks searchTopMeta
    P.render <$> "Branch" <> braces (sep $ punctuate ","
      [ "cost:" <+> pretty (sbCost branch)
      , "metas:" <+> prettyTCM (map goalMeta (sbGoals branch))
      , sep [ "instantiation:"
            , nest 2 $ pretty metaId <+> "=" <+> (prettyTCM =<< getMetaInstantiation metaId) ]
      , "used components:" <+> pretty (Map.toList $ sbComponentsUsed branch)
      ])


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
           , "hintSplitVars: Open" <+> pretty (openThing $ hintSplitVars comps)
           ]
         ]
    where
      prettyComp comp = pretty (compTerm comp) <+> ":" <+> pretty (compType comp)
      prettyOpenComp openComp = "Open" <+> parens (prettyComp $ openThing openComp)
      prettyTCMComp comp = prettyTCM (compTerm comp) <+> ":" <+> prettyTCM (compType comp)
      f = g prettyTCMComp
      g p n [] = n <> ": []"
      g p n xs = (n <> ":") $+$ nest 2 (vcat $ map p xs)


-- -- TODO: Is it possible to derive the pretty instances?
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

concatMapM :: Monad m => (a -> m [b]) -> [a] -> m [b]
concatMapM f = fmap concat . mapM f

reportSMDoc :: VerboseKey -> VerboseLevel -> SM Doc -> SM ()
reportSMDoc vk vl md = reportSDoc vk vl . runReaderT md =<< ask

mimerTrace :: Int -> VerboseLevel -> SM Doc -> SM ()
mimerTrace ilvl vlvl doc = reportSMDoc "mimer.trace" vlvl $ nest (2 * ilvl) $ "-" <+> doc

haskellRecord :: Doc -> [(Doc, Doc)] -> Doc
haskellRecord name fields = P.sep [ name, P.nest 2 $ P.braces (P.sep $ P.punctuate "," [ P.hang (k P.<+> "=") 2 v | (k, v) <- fields ]) ]

keyValueList :: [(Doc, Doc)] -> Doc
keyValueList kvs = P.braces $ P.sep $ P.punctuate "," [ P.hang (k P.<> ":") 2 v | (k, v) <- kvs ]

writeTime :: (MonadFail m, ReadTCState m, MonadError TCErr m, MonadTCM m, MonadDebug m) => InteractionId -> Maybe CPUTime -> m ()
writeTime ii mTime = do
  let time = case mTime of
        Nothing -> "n/a"
        Just (CPUTime t) -> show t
  file <- rangeFile . ipRange <$> lookupInteractionPoint ii
  case file of
    SMaybe.Nothing ->
      reportSLn "mimer.stats" 2 "No file found for interaction id"
    SMaybe.Just file -> do
      let path = filePath (rangeFilePath file) ++ ".stats"
      liftIO $ appendFile path (show (interactionId ii) ++ " " ++ time ++ "\n")

-- Hack to let you experiment with costs using verbosity flags.
customCosts :: TCM Costs
customCosts = do
  costLocal         <- cost "local"
  costFn            <- cost "fn"
  costDataCon       <- cost "dataCon"
  costRecordCon     <- cost "recordCon"
  costSpeculateProj <- cost "speculateProj"
  costProj          <- cost "proj"
  costAxiom         <- cost "axiom"
  costLet           <- cost "let"
  costLevel         <- cost "level"
  costSet           <- cost "set"
  costRecCall       <- cost "recCall"
  costNewMeta       <- cost "newMeta"
  costNewHiddenMeta <- cost "newHiddenMeta"
  compReuse         <- cost "compReuse"
  let costCompReuse uses = compReuse * uses ^ 2
  pure Costs{..}
  where
    cost key = getVerbosityLevel ("mimer-cost." ++ key)

getVerbosityLevel :: MonadDebug m => VerboseKey -> m VerboseLevel
getVerbosityLevel k = do
  t <- getVerbosity
  return $ case t of
    Strict.Nothing -> 1
    Strict.Just t
      | t == Trie.singleton [] 0 -> 0
      | otherwise -> lastWithDefault 0 $ Trie.lookupPath ks t
  where ks = parseVerboseKey k
