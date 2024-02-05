module Agda.Mimer.Mimer
  ( MimerResult(..)
  , mimer
  )
  where

import Control.DeepSeq (force, NFData(..))
import Control.Monad ((>=>), (=<<), unless, foldM, when, zipWithM, filterM)
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
import Agda.Syntax.Common.Pretty (Pretty, Doc, prettyShow, prettyList, render, pretty, braces, prettyList_, text, (<+>), nest, lbrace, rbrace, comma, ($$), vcat, ($+$), align, cat, parens)
import qualified Agda.Syntax.Concrete.Name as C
import Agda.Syntax.Info (exprNoRange)
import Agda.Syntax.Internal -- (Type, Type''(..), Term(..), Dom'(..), Abs(..), arity , ConHead(..), Sort'(..), Level, argFromDom, Level'(..), absurdBody, Dom, namedClausePats, Pattern'(..), dbPatVarIndex)
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
import Agda.TypeChecking.Pretty (MonadPretty, prettyTCM, PrettyTCM(..))
import Agda.TypeChecking.Records (isRecord, isRecursiveRecord)
import Agda.TypeChecking.Reduce (reduce, instantiateFull, instantiate)
import Agda.TypeChecking.Rules.LHS.Problem (AsBinding(..))
import Agda.TypeChecking.Rules.Term  (lambdaAddContext)
import Agda.TypeChecking.Substitute.Class (apply, applyE)
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
    reportDoc "mimer.top" 10 ("Running Mimer on interaction point" <+> pretty ii <+> "with argument string" <+> text (show argStr))

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
            reportSDoc "mimer.top" 10 $ do
              pSol <- prettyTCM sol
              return $ "Solution:" <+> pSol
            return sol

    putTC oldState

    stop <- liftIO $ getCPUTime
    let time = stop - start
    reportDoc "mimer.top" 10 ("Total elapsed time:" <+> pretty time)
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
  , goalEnv :: TCEnv
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
  , hintRecVars :: Open [Term]
  , hintSplitVars :: Open [Term]
  }
  deriving (Generic)

instance NFData BaseComponents

type CompId = Int
data Component = Component
  { compId :: CompId -- ^ Unique id for the component. Used for the cache.
  , compName :: Maybe Name -- ^ Used for keeping track of how many times a component has been used
  , compTerm :: Term
  , compType :: Type
  , compMetas :: [MetaId]
  , compCost :: Cost
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
    { compId = compId comp
    , compName = compName comp
    , compTerm = term
    , compType = typ
    , compMetas = compMetas comp
    , compCost = compCost comp
    }

-- | Create a goal in the current environment
mkGoal :: MonadTCEnv m => MetaId -> m Goal
mkGoal metaId = do
  env <- askTC
  return Goal
    { goalMeta = metaId
    , goalEnv = env
    }

mkGoalPreserveEnv :: Goal -> MetaId -> Goal
mkGoalPreserveEnv goalLocalSource metaId = Goal
  { goalMeta = metaId
  , goalEnv = goalEnv goalLocalSource
  }

mkComponent :: CompId -> [MetaId] -> Cost -> Maybe Name -> Term -> Type -> Component
mkComponent cId metaIds cost mName term typ = Component
  { compId = cId, compName = mName, compTerm = term, compType = typ, compMetas = metaIds, compCost = cost }

mkComponentQ :: CompId -> Cost -> QName -> Term -> Type -> Component
mkComponentQ cId cost qname = mkComponent cId [] cost (Just $ qnameName qname)

noName :: Maybe Name
noName = Nothing

newComponent :: MonadFresh CompId m => [MetaId] -> Cost -> Maybe Name -> Term -> Type -> m Component
newComponent metaIds cost mName term typ = fresh <&> \cId -> mkComponent cId metaIds cost mName term typ

newComponentQ :: MonadFresh CompId m => [MetaId] -> Cost -> QName -> Term -> Type -> m Component
newComponentQ metaIds cost qname term typ = fresh <&> \cId -> mkComponent cId metaIds cost (Just $ qnameName qname) term typ

addCost :: Cost -> Component -> Component
addCost cost comp = comp { compCost = cost + compCost comp }

addBranchGoals :: [Goal] -> SearchBranch -> SearchBranch
addBranchGoals goals branch = branch {sbGoals = goals ++ sbGoals branch}

withBranchState :: SearchBranch -> SM a -> SM a
withBranchState br ma = do
  putTC (sbTCState br)
  ma

withBranchAndGoal :: SearchBranch -> Goal -> SM a -> SM a
withBranchAndGoal br goal ma = {- withEnv (goalEnv goal) $ -}  withMetaId (goalMeta goal) $ withBranchState br ma

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
  let recVars = map fst . filter snd <$> lhsVars'
  lhsVars <- getOpen $ map fst <$> lhsVars'
  typedLocals <- getLocalVarTerms 0
  reportSDoc "mimer.components" 40 $ do
    vars <- prettyTCM lhsVars
    return $ "All LHS variables:" <+> vars <+> parens ("or" <+> pretty lhsVars)
  let typedLhsVars = filter (\(term,typ) -> term `elem` lhsVars) typedLocals
  reportSDoc "mimer.components" 40 $ do
    vars <- mapM prettyTCMTypedTerm typedLhsVars
    return $ "LHS variables with types:" <+> pretty vars <+> parens ("or"
      <+> pretty (map prettyTypedTerm typedLhsVars))
  -- TODO: For now, we *never* split on implicit arguments even if they are
  -- written explicitly on the LHS.
  splitVarsTyped <- filterM (\(term, typ) ->
                 ((argInfoHiding (domInfo typ) == NotHidden) &&) <$> isTypeDatatype (unDom typ))
               typedLhsVars
  reportSDoc "mimer.components" 40 $ do
    vars <- mapM prettyTCMTypedTerm splitVarsTyped
    return $ "Splitable variables" <+> pretty vars <+> parens ("or"
      <+> pretty (map prettyTypedTerm splitVarsTyped))

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
  components' <- foldM go components hintNames
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
      cId <- fresh -- TODO: We generate this id even if it is not used
      scope <- getScope
      case theDef info of
        Axiom{} | isToLevel typ -> return comps{hintLevel = mkComponentQ cId (costLevel costs) qname (Def qname []) typ : hintLevel comps}
                | shouldKeep scope -> return comps{hintAxioms = mkComponentQ cId (costAxiom costs) qname (Def qname []) typ : hintAxioms comps}
                | otherwise -> return comps
        -- TODO: Check if we want to use these
        DataOrRecSig{} -> return comps
        GeneralizableVar -> do
          return comps
        AbstractDefn{} -> do
          return comps
        -- If the function is in the same mutual block, do not include it.
        f@Function{}
          | Just qname == mDefName -> return comps{hintThisFn = Just $ mkComponentQ cId (costRecCall costs) qname (Def qname []) typ}
          | isToLevel typ && isNotMutual qname f
            -> return comps{hintLevel = mkComponentQ cId (costLevel costs) qname (Def qname []) typ : hintLevel comps}
          | isNotMutual qname f && shouldKeep scope
            -> return comps{hintFns = mkComponentQ cId (costFn costs) qname (Def qname []) typ : hintFns comps}
          | otherwise -> return comps
        Datatype{} -> return comps{hintDataTypes = mkComponentQ cId (costSet costs) qname (Def qname []) typ : hintDataTypes comps}
        Record{} -> do
          projections <- mapM (qnameToComponent (costSpeculateProj costs)) =<< getRecordFields qname
          return comps{ hintRecordTypes = mkComponentQ cId (costSet costs) qname (Def qname []) typ : hintRecordTypes comps
                      , hintProjections = projections ++ hintProjections comps}
        -- We look up constructors when we need them
        Constructor{} -> return comps
        -- TODO: special treatment for primitives?
        Primitive{} | isToLevel typ -> return comps{hintLevel = mkComponentQ cId (costLevel costs) qname (Def qname []) typ : hintLevel comps}
                    | shouldKeep scope -> return comps{hintFns = mkComponentQ cId (costFn costs) qname (Def qname []) typ : hintFns comps}
                    | otherwise -> return comps
        PrimitiveSort{} -> do
          return comps
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
      Def qname _ -> prettyShow qname == builtinLevelName
      _ -> False

    prettyTCMTypedTerm (term, typ) = do
      trm <- prettyTCM term
      ty <- prettyTCM typ
      return $ trm <+> ":" <+> ty

    prettyTypedTerm (term, typ) = pretty term <+> ":" <+> pretty typ

qnameToComponent :: (HasConstInfo tcm, ReadTCState tcm, MonadFresh CompId tcm, MonadTCM tcm)
  => Cost -> QName -> tcm Component
qnameToComponent cost qname = do
  info <- getConstInfo qname
  typ <- typeOfConst qname
  let term = case theDef info of
        Axiom{} -> Def qname []
        DataOrRecSig{} -> __IMPOSSIBLE__
        GeneralizableVar -> Def qname []
        AbstractDefn{} -> __IMPOSSIBLE__
        Function{} -> Def qname []
        Datatype{} -> Def qname []
        Record{} -> Def qname []
        c@Constructor{} -> Con (conSrcCon c) ConOCon []
        Primitive{} -> Def qname []
        PrimitiveSort{} -> Def qname []
  newComponentQ [] cost qname term typ

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
                mkComponent cId [] cost (Just name) term (unDom typ)

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
-- some constructor.
collectLHSVars :: (MonadFail tcm, ReadTCState tcm, MonadError TCErr tcm, MonadTCM tcm, HasConstInfo tcm)
  => InteractionId -> tcm (Open [(Term, Bool)])
collectLHSVars ii = do
  ipc <- ipClause <$> lookupInteractionPoint ii
  let fnName = ipcQName ipc
      clauseNr = ipcClauseNo ipc

  info <- getConstInfo fnName
  typ <- typeOfConst fnName
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

      reportSDoc "mimer" 60 $ do
        pITel <- prettyTCM iTel
        pCTel <- prettyTCM cTel
        return ("Tel:" $+$ nest 2 (pretty iTel $+$ pITel) $+$ "CTel:" $+$ nest 2 (pretty cTel $+$ pCTel))
      reportSDoc "mimer" 60 $ return $ "Shift:" <+> pretty shift

      -- TODO: Names (we don't use flex)
      let flex = concatMap (go False . namedThing . unArg) naps
          terms = map (\(n,i) -> (Var (n + shift) [], i)) flex
      makeOpen terms
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

  reportS "mimer.init" 15 (text "Interaction point in function:" <+> pretty mTheFunctionQName)
  reportS "mimer.init" 25 (text "Names in where-block" <+> pretty whereNames)

  metaId <- lookupInteractionId ii
  metaVar <- lookupLocalMeta metaId

  metaIds <- case mvInstantiation metaVar of
    InstV inst -> do

      metaIds <- allOpenMetas (instBody inst)

      -- TODO: Make pretty instantiation for 'Instantiation'?
      reportSLn "mimer.init" 20 $ "Interaction point already instantiated: " ++ prettyShow (instBody inst) ++ " with args " ++ prettyShow (instTel inst)

      -- ctx <- getContextTelescope
      return metaIds
    Open -> do
      reportSLn "mimer.init" 20 "Interaction point not instantiated."
      return [metaId]
    _ -> __IMPOSSIBLE__
  -- TODO: Print each meta-variable's full context telescope
  reportSDoc "mimer.init" 20 $ ("Remaining meta-variables to solve:" <+>) <$> prettyTCM metaIds
  reportSDoc "mimer.init" 20 $ ("Meta var args" <+>) <$> (prettyTCM =<< getMetaContextArgs metaVar)


  fnArgs1 <- withShowAllArguments' False $ getContextArgs >>= mapM prettyTCM
  fnArgs2 <- withShowAllArguments' True  $ getContextArgs >>= mapM prettyTCM
  let bringScope = map snd $ filter (uncurry (/=)) $ zip fnArgs1 fnArgs2
      bringScopeNoBraces = map (filter (`notElem` ['{', '}']) . render) bringScope
  reportDoc "mimer.temp" 20 $
    "Things to bring into scope:" $+$ nest 2 (
      "Context args (don't show):" <+> pretty fnArgs1 $+$
      "Context args (show all):  " <+> pretty fnArgs2 $+$
      "To bring into scope:      " <+> pretty bringScope $+$
      "To bring into scope (str):" <+> pretty bringScopeNoBraces
                                             )
  -- Check if there are any meta-variables to be solved
  case metaIds of
    -- No variables to solve, return the instantiation given
    [] -> do
      case mvInstantiation metaVar of
        InstV inst -> do
          expr <- withInteractionId ii $ do
            metaArgs <- getMetaContextArgs metaVar
            instantiateFull (apply (MetaV metaId []) metaArgs) >>= reify
          str <- render <$> prettyTCM expr
          let sol = MimerExpr str
          reportDoc "mimer.init" 10 $ "Goal already solved. Solution:" <+> text str
          return [sol]
        _ -> __IMPOSSIBLE__
    _ -> do
      costs <- ifM (hasVerbosity "mimer.cost.custom" 10)
                 {- then -} customCosts
                 {- else -} (return defaultCosts)
      reportDoc "mimer.cost.custom" 10 $ "Using costs:" $+$ nest 2 (pretty costs)
      components <- collectComponents options costs ii mTheFunctionQName whereNames metaId

      state <- getTC
      env <- askTC

      startGoals <- mapM mkGoal metaIds
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

      reportSDoc "mimer.init" 20 $ do
        opts <- prettyTCM searchOptions
        return $ "Using search options:" $+$ nest 2 opts
      reportDoc "mimer.init" 20 ("Initial search branch:" $+$ nest 2 (pretty startBranch))

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

                reportSMDoc "mimer.search" 40 $ do
                  inst <- branchInstantiationDocCost branch
                  metas <- prettyTCM $ map goalMeta $ sbGoals branch
                  return $
                    "Choosing branch with instantiation:" $+$ nest 2
                    (inst $+$ "..and remaining metas:" <+> pretty metas)
                reportDoc "mimer.search" 50 $ "Full branch:" <+> pretty branch
                reportSMDoc "mimer.search" 45 $ do
                  is <- mapM branchInstantiationDocCost $ Q.toAscList branchQueue'
                  return $ "Instantiation of other branches:" <+> prettyList is

                let elapsed = time - startTime
                if elapsed < timeout
                then do
                  (newBranches, sols) <- refine branch >>= partitionStepResult
                  let branchQueue'' = foldr Q.insert branchQueue' newBranches
                  reportSLn "mimer.search" 40 $ show (length sols) ++ " solutions found during cycle " ++ show (n + 1)
                  reportSMDoc "mimer.search" 45 $ ("Solutions:" <+>) <$> prettyTCM sols
                  reportSMDoc "mimer.search" 45 $ do
                     is <- mapM branchInstantiationDocCost newBranches
                     return $ "New branch instantiations:" <+> prettyList is

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
        reportSDoc "mimer.search" 15 $ do
          solDocs <- mapM prettyTCM sols
          return $ "Solutions found: " <+> pretty solDocs
        reportSMDoc "mimer.stats" 10 $ do
          ref <- asks searchStats
          stats <- liftIO $ readIORef ref
          return $ "Statistics:" <+> text (show stats)
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
      reportSDoc "mimer.components" 20 $ do
        cxt <- getContextTelescope
        return $ "No cache found checkpoint:" <+> pretty checkpoint
          $+$ nest 2 ("with context:" <+> pretty cxt)
      -- Generate components for this context
      comps <- genComponents
      reportDoc "mimer.components" 20 $ "Generated" <+> pretty (sum $ map (length . snd) comps) <+> "components"
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
  recCalls <- genRecCalls >>= genAddSource (searchGenProjectionsRec opts)
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
genComponentsFrom False comp = do
  comp' <- applyToMetasG 0 Nothing comp
  return [comp']
genComponentsFrom appRecElims origComp = do
  comp <- applyToMetasG 0 Nothing origComp
  if appRecElims
  then go' Set.empty comp
  else return [comp]
  where
  go' :: Set QName -> Component -> SM [Component]
  go' seenRecords comp = do
    projComps <- getRecordInfo (compType comp) >>= \case
      Nothing -> return []
      Just (recordName, args, fields, isRecursive)
          | Set.member recordName seenRecords -> do
              reportDoc "mimer.components" 60 $
                "Skipping projection because recursive record already seen:" <+> pretty recordName
              return []
          | otherwise -> do
              let seenRecords' = if isRecursive then Set.insert recordName seenRecords else seenRecords
              comps <- mapM (applyProj args comp >=> applyToMetasG 0 Nothing) fields
              concatMapM (go' seenRecords') comps
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
  reportDoc "mimer.temp" 10 $ "applyProj: newTerm =" <+> pretty newTerm
  projType <- defType <$> getConstInfo qname
  projTypeWithArgs <- piApplyM projType recordArgs
  newType <- piApplyM projTypeWithArgs (compTerm comp')
  reportSDoc "mimer.temp" 10 $ do
    ter <- instantiateFull newTerm >>= prettyTCM
    typ <- instantiateFull newType >>= prettyTCM
    return $ "After projection:" <+> ter <+> typ
  newComponentQ (compMetas comp') (compCost comp' + cost) qname newTerm newType


-- TODO: currently reducing twice
applyToMetasG
  :: Nat -- ^ Arguments to skip applying term. Used for record parameters.
  -> Maybe Nat -- ^ Max number of arguments to apply.
  -> Component -> SM Component
applyToMetasG _ (Just m) comp | m <= 0 = return comp
applyToMetasG skip maxArgs comp = do
  ctx <- getContextTelescope
  compTyp <- reduce $ compType comp
  case unEl compTyp of
    Pi dom abs -> do
      let domainType = unDom dom
      (metaId, metaTerm) <- createMeta domainType
      let arg = setOrigin Inserted $ metaTerm <$ argFromDom dom
      newType <- reduce =<< piApplyM (compType comp) metaTerm
      -- For records, the parameters are not included in the term
      let newTerm = if skip > 0 then compTerm comp else apply (compTerm comp) [arg]
      cost <- asks $ (if getHiding arg == Hidden then costNewHiddenMeta else costNewMeta) . searchCosts
      applyToMetasG (predNat skip) (predNat <$> maxArgs)
                    comp{ compTerm = newTerm
                        , compType = newType
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
    metaType <- getMetaTypeInContext metaId
    return $ "Created meta-variable (type in context):" <+> pretty metaTerm <+> ":" <+> pretty metaType
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
      str <- render <$> prettyTCM exp
      return $ (brs', MimerExpr str : sols)
    ResultClauses cls -> do
      f <- fromMaybe __IMPOSSIBLE__ <$> asks searchFnName
      return $ (brs', MimerClauses f cls : sols)


topInstantiationDoc :: SM Doc
topInstantiationDoc = asks searchTopMeta >>= getMetaInstantiation >>= maybe (return "(nothing)") prettyTCM

branchInstantiationDocCost :: SearchBranch -> SM Doc
branchInstantiationDocCost branch = do
  inst <- branchInstantiationDoc branch
  return $ inst <+> parens ("cost =" <+> pretty (sbCost branch))

-- | For debug
branchInstantiationDoc :: SearchBranch -> SM Doc
branchInstantiationDoc branch = withBranchState branch topInstantiationDoc

refine :: SearchBranch -> SM [SearchStepResult]
refine branch = withBranchState branch $ do
  (goal1, branch1) <- nextBranchMeta' branch

  reportDoc "mimer.refine" 20 $ "Refining goal" <+> pretty goal1

  withBranchAndGoal branch1 goal1 $ do
    goalType1 <- bench [Bench.Reduce] $ reduce =<< getMetaTypeInContext (goalMeta goal1)

    reportDoc "mimer.refine" 30 $ "Goal type:" <+> pretty goalType1
    reportSDoc "mimer.refine" 30 $ ("Goal context:" <+>) . pretty <$> getContextTelescope

    -- Lambda-abstract as far as possible
    tryLamAbs goal1 goalType1 branch1 >>= \case
      -- Abstracted with absurd pattern: solution found.
      Left expr -> do
        reportSDoc "mimer.refine" 30 $ ("Abstracted with absurd lambda. Result: " <+>) <$> prettyTCM expr
        return [ResultExpr expr]
      -- Normal abstraction
      Right (goal2, goalType2, branch2) -> withBranchAndGoal branch2 goal2 $ do
        -- Make sure we can do recursive calls without getting errors
        (goal3, branch3) <- ensureNoOccursCheck goal2 goalType2 branch2
        let goalType3 = goalType2
        withBranchAndGoal branch3 goal3 $ do
          (branch4, components) <- prepareComponents goal3 branch3
          withBranchAndGoal branch4 goal3 $ do
            reportSMDoc "mimer.temp" 10 $ do
              subst <- checkpointSubstitution =<< asks searchTopCheckpoint
              return $ "Substitution after abstraction:" <+> pretty subst

            reportSDoc "mimer.refine" 40 $ getContextTelescope >>= \tel -> return $
              "After lambda abstract:" <+> nest 2 (vcat
                                                  [ "Goal:" <+> pretty goal3
                                                  , "Goal type:" <+> pretty goalType3
                                                  , "Goal context:" <+> pretty tel])
            reportSMDoc "mimer.components" 50 $ do
              comps <- mapM prettyTCM $ concatMap snd components
              return $ "Components:" $+$ nest 2 (vcat $ comps)

            results1 <- tryComponents goal3 goalType3 branch4 components
            results2 <- tryDataRecord goal3 goalType3 branch4
            return $ results1 ++ results2

tryFns :: Goal -> Type -> SearchBranch -> SM [SearchStepResult]
tryFns goal goalType branch = withBranchAndGoal branch goal $ do
  reportDoc "mimer.refine.fn" 50 $ "Trying functions"
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
        let bindName = absName abs
        newName <- freshName_ bindName
        (metaId', bodyType, metaTerm, env) <- lambdaAddContext newName bindName dom $ do
          goalType' <- getMetaTypeInContext (goalMeta goal)
          bodyType <- bench [Bench.Reduce] $ reduce =<< piApplyM goalType' (Var 0 []) -- TODO: Good place to reduce?
          (metaId', metaTerm) <- bench [Bench.Free] $ newValueMeta DontRunMetaOccursCheck CmpLeq bodyType
          env <- askTC

          ctx <- getContextTelescope
          return (metaId', bodyType, metaTerm, env)

        let argInf = domInfo dom -- TODO: is this the correct arg info?
            newAbs = Abs{absName = bindName, unAbs = metaTerm } --MetaV metaId' [] }
            -- look at mkLam
            term = Lam argInf newAbs

        newMetaIds <- assignMeta (goalMeta goal) term goalType

        withEnv env $ do
          branch' <- updateBranch newMetaIds branch
          goal' <- mkGoal metaId'
          tryLamAbs goal' bodyType branch'
    _ -> do
      branch' <- updateBranch [] branch -- TODO: Is this necessary?
      return $ Right (goal, goalType, branch')


genRecCalls :: SM [Component]
genRecCalls = asks (hintThisFn . searchBaseComponents) >>= \case
  -- If the hole is, e.g., in a type signature, recursive calls are not possible
  Nothing -> return []
  -- TODO: Make sure there are no pruning problems
  Just thisFn -> asks (hintRecVars . searchBaseComponents) >>= getOpen >>= \case
    -- No candidate arguments for a recursive call
    [] -> return []
    recCandTerms -> do
      Costs{..} <- asks searchCosts
      n <- localVarCount
      localVars <- lift $ getLocalVars n costLocal
      let recCands = filter (\t -> case compTerm t of v@Var{} -> v `elem` recCandTerms; _ -> False) localVars

      let newRecCall = do
            -- Apply the recursive call to new metas
            (thisFnTerm, thisFnType, newMetas) <- applyToMetas 0 (compTerm thisFn) (compType thisFn)
            argGoals <- mapM mkGoal newMetas
            comp <- newComponent newMetas (compCost thisFn) (compName thisFn) thisFnTerm thisFnType
            return (comp, argGoals)

          -- go :: Component -- ^ Recursive call function applied to meta-variables
          --   -> [Goal] -- ^ Remaining parameters to try to fill
          --   -> [Component] -- ^ Remaining argument candidates for the current parameter
          --   -> SM [Component]
          go _thisFn [] _args = return []
          go thisFn (goal:goals) [] = go thisFn goals recCands
          go thisFn (goal:goals) (arg:args) = do
            reportSMDoc "mimer.components" 80 $ do
              term <- prettyTCM (compTerm thisFn)
              argTerm <- prettyTCM (compTerm arg)
              gm <- prettyTCM (goalMeta goal)
              return $ "Trying to generate recursive call" <+> term <+> "with" <+> argTerm <+> "for" <+> gm
            goalType <- getMetaTypeInContext (goalMeta goal)
            state <- getTC
            tryRefineWith' goal goalType arg >>= \case
              Nothing -> do
                putTC state
                go thisFn (goal:goals) args
              Just (newMetas1, newMetas2) -> do
                let newComp = thisFn{compMetas = newMetas1 ++ newMetas2 ++ (compMetas thisFn \\ [goalMeta goal])}
                (thisFn', goals') <- newRecCall
                (newComp:) <$> go thisFn' (drop (length goals' - length goals - 1) goals') args
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

-- HACK: If the meta-variable is set to run occurs check, assigning a
-- recursive call to it will cause an error. Therefore, we create a new
-- meta-variable with the check disabled and assign it to the previous
-- one.
ensureNoOccursCheck :: Goal -> Type -> SearchBranch -> SM (Goal, SearchBranch)
ensureNoOccursCheck goal goalType branch = do
  metaVar <- lookupLocalMeta (goalMeta goal)
  if miMetaOccursCheck (mvInfo metaVar) == DontRunMetaOccursCheck
  then do
    reportDoc "mimer.refine.rec" 60 $ "Meta-variable already has DontRunMetaOccursCheck"
    return (goal, branch)
  else do
    metaArgs <- getMetaContextArgs metaVar
    (newMetaId, newMetaTerm) <- newValueMeta DontRunMetaOccursCheck CmpLeq goalType
    assignV DirLeq (goalMeta goal) metaArgs newMetaTerm (AsTermsOf goalType)
    reportDoc "mimer.refine.rec" 60 $ "Instantiating meta-variable (" <> pretty (goalMeta goal) <> ") with a new one with DontRunMetaOccursCheck (" <> pretty newMetaId <> ")"
    branch' <- updateBranch [] branch
    return (goal{goalMeta = newMetaId}, branch')


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
        | prettyShow qname == "Agda.Primitive.Level" -> do
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
      let cHead = recConHead recordDefn
          cName = conName cHead
          cTerm = Con cHead ConOSystem []
      cType <- typeOfConst cName
      cost <- asks (costRecordCon . searchCosts) -- TODO: Use lenses for this?
      comp <- newComponentQ [] cost cName cTerm cType
      -- -- NOTE: at most 1
      newBranches <- maybeToList <$> tryRefineAddMetasSkip (recPars recordDefn) goal goalType branch comp
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
              comp <- newComponent [] cost Nothing (Sort $ Type $ Max (i - 1) []) goalType
              return [(branch, comp)]
          | otherwise -> return []
        (Max i ps) -> do
              (metaId, metaTerm) <- createMeta =<< levelType
              comp <- newComponent [metaId] cost Nothing (Sort $ Type $ Max (max 0 (i - 1)) [Plus 0 metaTerm]) goalType
              branch' <- updateBranch [metaId] branch
              return [(branch', comp)]
      reportSDoc "mimer.refine.set" 40 $ do
        st <- prettyTCM (map snd setCandidates)
        ty <- prettyTCM goalType
        return $ "Trying" <+> st <+> "for" <+> ty
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
  reportSMDoc "mimer.refine" 50 $ do
    cxt <- getContextTelescope >>= prettyTCM
    hi <- prettyTCM $ compTerm comp
    ht <- prettyTCM $ compType comp
    gm <- prettyTCM $ goalMeta goal
    gt <- prettyTCM goalType
    return $ "Trying refinement" <+> hi <+> ":" <+> ht $+$ nest 2 ("for" <+> gm <+> ":" <+> gt $+$ "in context" <+> cxt)

  metasCreatedBy (dumbUnifier (compType comp) goalType) >>= \case
    (True, newMetaStore) -> do
      updateStat incRefineSuccess
      -- TODO: Why is newMetaIds not used here?
      newMetaIds <- assignMeta (goalMeta goal) (compTerm comp) goalType
      let newMetaIds' = Map.keys (openMetas newMetaStore)
      reportSDoc "mimer.refine" 60 $ do
        ms <- prettyTCM newMetaIds
        return $ "Refine: assignMeta created new metas:" <+> ms

      reportSMDoc "mimer.refine" 50 $ "Refinement succeeded"
      -- Take the metas stored in the component and add them as sub-goals
      Just <$> updateBranchCost comp (newMetaIds' ++ compMetas comp) branch
    (False, _) -> do
      updateStat incRefineFail
      reportSMDoc "mimer.refine" 50 $ "Refinement failed"
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
tryRefineAddMetasSkip :: Nat -> Goal -> Type -> SearchBranch -> Component -> SM (Maybe SearchBranch)
tryRefineAddMetasSkip skip goal goalType branch comp = withBranchAndGoal branch goal $ do
  -- Apply the hint to new metas (generating @c@, @c ?@, @c ? ?@, etc.)
  -- TODO: Where is the best place to reduce the hint type?
  comp' <- applyToMetasG skip Nothing comp
  branch' <- updateBranch [] branch
  tryRefineWith goal goalType branch' comp'

tryRefineAddMetas :: Goal -> Type -> SearchBranch -> Component -> SM (Maybe SearchBranch)
tryRefineAddMetas = tryRefineAddMetasSkip 0

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
        goals' <- mapM mkGoal metaIds
        return $ OpenBranch $ branch{sbGoals = reverse goals'}

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
  newGoals <- mapM mkGoal newMetaIds
  return branch{ sbTCState = state
               , sbGoals = newGoals ++ sbGoals branch
               , sbCost = sbCost branch + deltaCost
               , sbComponentsUsed = compsUsed'
               }

updateBranch :: [MetaId] -> SearchBranch -> SM SearchBranch
updateBranch = updateBranch' Nothing

updateBranchCost :: Component -> [MetaId] -> SearchBranch -> SM SearchBranch
updateBranchCost comp = updateBranch' (Just comp)

assignMeta :: MetaId -> Term -> Type -> SM [MetaId]
assignMeta metaId term metaType = bench [Bench.CheckRHS] $
  metasCreatedBy (do
    metaVar <- lookupLocalMeta metaId
    metaArgs <- getMetaContextArgs metaVar

    reportSMDoc "mimer.assignMeta" 60 $ do
      cxt <- getContextTelescope
      return $ "Assigning" <+> pretty term $+$ nest 2 ("to" <+> pretty metaId <+> ":" <+> pretty metaType $+$ "in context" <+> pretty cxt)

    (assignV DirLeq metaId metaArgs term (AsTermsOf metaType)) `catchError` \err -> do
      reportSMDoc "mimer.assignMeta" 30 $ do
        er <- prettyTCM err
        cxt <- getContextTelescope
        return $ "Got error from assignV:" <+> er $+$ nest 2 ("when trying to assign" <+> pretty term $+$ "to" <+> pretty metaId <+> ":" <+> pretty metaType $+$ "in context" <+> pretty cxt)) >>= \case
        ((), newMetaStore) -> do
          let newMetaIds = Map.keys (openMetas newMetaStore)
          return newMetaIds

dumbUnifier :: Type -> Type -> SM Bool
dumbUnifier t1 t2 = bench [Bench.UnifyIndices] $ do
  updateStat incTypeEqChecks
  (noConstraints $ equalType t2 t1 >> return True) `catchError` \err -> do
    reportSDoc "mimer.unify" 80 $ do
      str <- prettyTCM err
      return $ "Unification failed with error:" <+> str
    return False

-- Duplicate of a local definition in Agda.Interaction.BasicOps
showTCM :: (MonadPretty tcm, PrettyTCM a) => a -> tcm String
showTCM v = render <$> prettyTCM v

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
  mapM (\(term, domTyp) -> newComponent [] (cost - varZeroDiscount term) noName term (unDom domTyp)) typedTerms

getLocalVarTerms :: Int -> TCM [(Term, Dom Type)]
getLocalVarTerms localCxt = do
  contextTerms <- getContextTerms
  contextTypes <- flattenTel <$> getContextTelescope
  let inScope i _ | i < localCxt = pure True   -- Ignore scope for variables we inserted ourselves
      inScope _ Dom{ unDom = (name, _) } = do
        x <- abstractToConcrete_ name
        pure $ C.isInScope x == C.InScope
  scope <- mapM (uncurry inScope) . reverse . zip [0..] =<< getContext
  return [ e | (True, e) <- zip scope $ zip contextTerms contextTypes ]



prettyBranch :: SearchBranch -> SM String
prettyBranch branch = withBranchState branch $ do
    metas <- prettyTCM $ map goalMeta (sbGoals branch)
    metaId <- asks searchTopMeta
    inst <- getMetaInstantiation metaId
    instStr <- prettyTCM inst
    let compUses = pretty $ Map.toList $ sbComponentsUsed branch
    return $ render $ text "Branch{cost: " <> text (show $ sbCost branch) <> ", metas: " <> metas <> text " , instantiation: " <> pretty metaId <> text " = " <> instStr <> text ", used components: " <> compUses <> text "}"


instance Pretty Goal where
  pretty goal = keyValueList
    [ ("goalMeta", pretty $ goalMeta goal)
    , ("goalEnv", "[...]")
    ]

instance Pretty SearchBranch where
  pretty branch = keyValueList
    [ ("sbTCState", "[...]")
    , ("sbGoals", pretty $ sbGoals branch)
    , ("sbCost", pretty $ sbCost branch)
    , ("sbComponentsUsed", pretty $ sbComponentsUsed branch)
    ]


instance PrettyTCM BaseComponents where
  prettyTCM comps = do
    let thisFn = case hintThisFn comps of
          Nothing -> "(nothing)"
          Just comp -> prettyComp comp
    recVars <- prettyTCM =<< getOpen (hintRecVars comps)
    content <- sequence
      [ f "hintFns" (hintFns comps)
      , f "hintDataTypes" (hintDataTypes comps)
      , f "hintRecordTypes" (hintRecordTypes comps)
      , f "hintAxioms" (hintAxioms comps)
      , f "hintLevel" (hintLevel comps)
      , f "hintProjections" (hintProjections comps)
      , return $ "hintThisFn:" <+> thisFn
      , g (return . prettyOpenComp) "hintLetVars" (hintLetVars comps)
      , return $ "hintRecVars: Open" <+> pretty (openThing $ hintRecVars comps)
      , return $ "hintSplitVars: Open" <+> pretty (openThing $ hintSplitVars comps)
      ]
    return $ "Base components:" $+$ nest 2 (vcat content)
    where
      prettyComp comp = pretty (compTerm comp) <+> ":" <+> pretty (compType comp)
      prettyOpenComp openComp = "Open" <+> parens (prettyComp $ openThing openComp)
      prettyTCMComp comp = do
        term <- prettyTCM (compTerm comp)
        typ <- prettyTCM (compType comp)
        return $ term <+> ":" <+> typ
      f = g prettyTCMComp
      g p n [] = return $ n <> ": []"
      g p n xs = do
        cmps <- mapM p xs
        return $ (n <> ":") $+$ nest 2 (vcat cmps)


-- -- TODO: Is it possible to derive the pretty instances?
instance Pretty BaseComponents where
  pretty comps = cat
      [ f "hintFns" (hintFns comps)
      , f "hintDataTypes" (hintDataTypes comps)
      , f "hintRecordTypes" (hintRecordTypes comps)
      , f "hintAxioms" (hintAxioms comps)
      , f "hintLevel" (hintLevel comps)
      , f "hintProjections" (hintProjections comps)
      ]
    where
      f n [] = n <> ": []"
      f n xs = (n <> ":") $+$ nest 2 (pretty xs)

instance Pretty SearchOptions where
  pretty opts =
    "searchBaseComponents:" $+$ nest 2 (pretty $ searchBaseComponents opts) $+$
    keyValueList
      [ ("searchHintMode", pretty $ searchHintMode opts)
      , ("searchTimeout", pretty $ searchTimeout opts)
      , ("searchTopMeta", pretty $ searchTopMeta opts)
      , ("searchTopEnv", "[...]")
      ] $+$
      "searchCosts:" $+$ nest 2 (pretty $ searchCosts opts)

instance PrettyTCM SearchOptions where
  prettyTCM opts = do
    comps <- prettyTCM $ searchBaseComponents opts
    topMeta <- prettyTCM $ searchTopMeta opts
    checkpoint <- prettyTCM $ searchTopCheckpoint opts
    return $ "searchBaseComponents:" $+$ nest 2 comps $+$
      vcat
        [ "searchHintMode:" <+> pretty (searchHintMode opts)
        , "searchTimeout:" <+> pretty (searchTimeout opts)
        , "searchTopMeta:" <+> topMeta
        , "searchTopEnv: [...]"
        , "searchTopCheckpoint:" <+> checkpoint
        , "searchInteractionId:" <+> pretty (searchInteractionId opts)
        , "searchFnName:" <+> pretty (searchFnName opts)
        , "searchStats: [...]"
        ] $+$
        "searchCosts:" $+$ nest 2 (pretty $ searchCosts opts)

instance Pretty Component where
  pretty comp = haskellRecord "Component"
    [ ("compId", pretty $ compId comp)
    , ("compTerm", pretty $ compTerm comp)
    , ("compType", pretty $ compType comp)
    , ("compMetas", pretty $ compMetas comp)
    , ("compCost", pretty $ compCost comp)
    ]

instance Pretty Costs where
  pretty costs = align 20 entries
    where
      entries =
        [ ("costLocal:"         , pretty $ costLocal costs)
        , ("costFn:"            , pretty $ costFn costs)
        , ("costDataCon:"       , pretty $ costDataCon costs)
        , ("costRecordCon:"     , pretty $ costRecordCon costs)
        , ("costSpeculateProj:" , pretty $ costSpeculateProj costs)
        , ("costProj:"          , pretty $ costProj costs)
        , ("costAxiom:"         , pretty $ costAxiom costs)
        , ("costLet:"           , pretty $ costLet costs)
        , ("costLevel:"         , pretty $ costLevel costs)
        , ("costSet:"           , pretty $ costSet costs)
        , ("costRecCall:"       , pretty $ costRecCall costs)
        , ("costNewMeta:"       , pretty $ costNewMeta costs)
        , ("costNewHiddenMeta:" , pretty $ costNewHiddenMeta costs)
        , ("costCompReuse:"     , text "{function}")
        ]

instance PrettyTCM Component where
  prettyTCM comp = do
    term <- prettyTCM $ compTerm comp
    typ <- prettyTCM $ compType comp
    metas <- prettyTCM $ compMetas comp
    return $ pretty (compId comp) <+> "=" <+> term <+> ":" <+> typ <+> "with meta-variables" <+> metas <+> "and cost" <+> pretty (compCost comp)


instance PrettyTCM MimerResult where
  prettyTCM = \case
    MimerExpr expr -> return $ "MimerExpr" <+> pretty expr
    MimerClauses f cl -> return $ "MimerClauses" <+> pretty f <+> "[..]" -- TODO: display the clauses
    MimerNoResult -> return "MimerNoResult"
    MimerList sols -> return $ "MimerList" <+> pretty sols

concatMapM :: Monad m => (a -> m [b]) -> [a] -> m [b]
concatMapM f = fmap concat . mapM f

-- TODO: Ask how they typically do it
reportDoc :: MonadDebug m => VerboseKey -> VerboseLevel -> Doc -> m ()
reportDoc vk vl d = reportSDoc vk vl (return d)

reportSMDoc :: VerboseKey -> VerboseLevel -> SM Doc -> SM ()
reportSMDoc vk vl md = md >>= reportDoc vk vl

encloseSep
    :: Doc   -- ^ left delimiter
    -> Doc   -- ^ right delimiter
    -> Doc   -- ^ separator
    -> [Doc] -- ^ input documents
    -> Doc
encloseSep l r s ds = case ds of
    []  -> l <> r
    [d] -> l <> d <> r
    _   -> cat (zipWith (<>) (l : repeat s) ds) <> r

haskellList :: [Doc] -> Doc
haskellList = encloseSep "[ " " ]" ", "

haskellRecord :: Doc -> [(Doc, Doc)] -> Doc
haskellRecord name fields = name <+> sepList " = " fields

keyValueList :: [(Doc, Doc)] -> Doc
keyValueList = sepList ": "

sepList :: Doc -> [(Doc, Doc)] -> Doc
sepList s values = encloseSep "{ " " }" ", " $ map (\(n, v) -> n <> s <> v) values


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
    cost key = getVerbosityLevel ("mimer.cost." ++ key)

getVerbosityLevel :: MonadDebug m => VerboseKey -> m VerboseLevel
getVerbosityLevel k = do
  t <- getVerbosity
  return $ case t of
    Strict.Nothing -> 1
    Strict.Just t
      | t == Trie.singleton [] 0 -> 0
      | otherwise -> lastWithDefault 0 $ Trie.lookupPath ks t
  where ks = parseVerboseKey k
