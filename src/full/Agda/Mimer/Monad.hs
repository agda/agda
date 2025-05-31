
module Agda.Mimer.Monad where

import Control.DeepSeq (NFData(..))
import Control.Monad
import Control.Monad.Except (catchError, MonadError)
import Control.Monad.IO.Class (liftIO)
import Control.Monad.Reader (ReaderT(..), asks, ask, lift)
import Data.IORef (modifyIORef')
import Data.Map qualified as Map
import Data.List qualified as List
import Data.List.NonEmpty qualified as NonEmptyList (head)
import Data.Maybe

import Agda.Syntax.Common
import Agda.Syntax.Common.Pretty qualified as P
import Agda.Syntax.Internal
import Agda.Syntax.Position (rangeFile, rangeFilePath)
import Agda.Syntax.Concrete.Name qualified as C
import Agda.Syntax.Abstract (Expr)
import Agda.Syntax.Abstract qualified as A
import Agda.Syntax.Abstract.Views qualified as A
import Agda.Syntax.Internal.MetaVars (AllMetas(..))
import Agda.Syntax.Translation.AbstractToConcrete (abstractToConcrete_)
import Agda.Syntax.Translation.InternalToAbstract (reify, blankNotInScope)
import Agda.Syntax.Scope.Base qualified as Scope
import Agda.TypeChecking.Monad
import Agda.TypeChecking.MetaVars (newValueMeta)
import Agda.TypeChecking.Primitive (getBuiltinName)
import Agda.TypeChecking.Datatypes (isDataOrRecord)
import Agda.TypeChecking.Reduce (reduce, instantiateFull, instantiate)
import Agda.TypeChecking.Records (isRecord)
import Agda.TypeChecking.Pretty
import Agda.TypeChecking.Conversion (equalType)
import Agda.TypeChecking.Constraints (noConstraints)
import Agda.TypeChecking.Telescope (flattenTel, piApplyM)
import Agda.TypeChecking.Substitute (pattern TelV, telView', piApply, apply, applyE, NoSubst(..))
import Agda.Interaction.BasicOps (normalForm)
import Agda.Benchmarking qualified as Bench
import Agda.Utils.Benchmark (billTo)
import Agda.Utils.Functor ((<&>), (<.>))
import Agda.Utils.FileName (filePath)
import Agda.Utils.Impossible
import Agda.Utils.Maybe.Strict qualified as SMaybe
import Agda.Utils.Time (CPUTime(..))

import Agda.Mimer.Options
import Agda.Mimer.Types

type SM a = ReaderT SearchOptions TCM a

------------------------------------------------------------------------
-- * Agda internals
------------------------------------------------------------------------

getRecordFields :: (HasConstInfo tcm, MonadTCM tcm) => QName -> tcm [QName]
getRecordFields = fmap (map unDom . recFields . theDef) . getConstInfo

getRecordInfo :: (MonadTCM tcm, HasConstInfo tcm) => Type
              -> tcm (Maybe ( QName     -- Record name
                           , Args      -- Record parameters converted to (hidden) arguments
                           , [QName]   -- Field names
                           , Bool      -- Is recursive?
                           ))
getRecordInfo typ = case unEl typ of
  Def qname elims -> isRecord qname >>= \case
    Nothing -> return Nothing
    Just defn -> do
      fields <- getRecordFields qname
      return $ Just (qname, argsFromElims elims, fields, recRecursive_ defn)
  _ -> return Nothing

allOpenMetas :: (AllMetas t, ReadTCState tcm) => t -> tcm [MetaId]
allOpenMetas t = do
  openMetas <- getOpenMetas
  return $ allMetas (:[]) t `List.intersect` openMetas

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

-- TODO: Rename (see metaInstantiation)
getMetaInstantiation :: (MonadTCM tcm, PureTCM tcm, MonadDebug tcm, MonadInteractionPoints tcm, MonadFresh NameId tcm)
  => MetaId -> tcm (Maybe Expr)
getMetaInstantiation = metaInstantiation >=> traverse (instantiateFull >=> reify)

metaInstantiation :: (MonadTCM tcm, MonadDebug tcm, ReadTCState tcm) => MetaId -> tcm (Maybe Term)
metaInstantiation metaId = lookupLocalMeta metaId <&> mvInstantiation >>= \case
  InstV inst -> return $ Just $ instBody inst
  _ -> return Nothing

-- TODO: why not also accept pattern record types here?
isTypeDatatype :: (MonadTCM tcm, MonadReduce tcm, HasConstInfo tcm) => Type -> tcm Bool
isTypeDatatype typ = liftTCM do
  reduce typ <&> unEl >>= isDataOrRecord <&> \case
    Just (_, IsData) -> True
    _ -> False

-- | Is an element of the given type computing a level?
--
-- The returned checker is only sound but not complete because the type is taken as-is
-- rather than being reduced.
endsInLevelTester :: TCM (Type -> Bool)
endsInLevelTester = do
  getBuiltinName builtinLevel >>= \case
    Nothing    -> return $ const False
    Just level -> return \ t ->
      -- NOTE: We do not reduce the type before checking, so some user definitions
      -- will not be included here.
      case telView' t of
        TelV _ (El _ (Def x _)) -> x == level
        _ -> False

-- | From the scope of the given meta variable,
--   extract all names in scope that we could use during synthesis.
--   (This excludes macros, generalizable variables, pattern synonyms.)
getEverythingInScope :: MetaVariable -> [QName]
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
  qnames

-- TODO: Make sure the type is reduced the first time this is called
-- TODO: Rewrite with Component?
-- NOTE: The new metas are in left-to-right order -- the opposite of the
-- order they should be solved in.
applyToMetas :: Nat -> Term -> Type -> TCM (Term, Type, [MetaId])
applyToMetas skip term typ = do
  ctx <- getContextTelescope
  case unEl typ of
    Pi dom abs -> do
      let domainType = unDom dom
      -- TODO: What exactly does the occur check do?
      (metaId', metaTerm) <- newValueMeta DontRunMetaOccursCheck CmpLeq domainType
      let arg = setOrigin Inserted $ metaTerm <$ argFromDom dom
      newType <- reduce =<< piApplyM typ metaTerm -- TODO: Is this the best place to reduce?
      -- For records, the parameters are not included in the term
      let newTerm = if skip > 0 then term else apply term [arg]
      (term', typ', metas) <- applyToMetas (max 0 $ skip - 1) newTerm newType
      return (term', typ', metaId' : metas)
    _ -> return (term, typ, [])

------------------------------------------------------------------------
-- * Components
------------------------------------------------------------------------

localVarCount :: SM Int
localVarCount = do
  top <- asks $ length . envContext . searchTopEnv
  cur <- length <$> getContext
  pure $ cur - top

getOpenComponent :: (MonadTCM tcm, MonadDebug tcm) => Open Component -> tcm Component
getOpenComponent openComp = do
  let comp = openThing openComp
  reportSDoc "mimer.components.open" 40 $ "Opening component" <+> prettyTCM (compId comp) <+> prettyTCM (compName comp)
  term <- getOpen $ compTerm <$> openComp
  reportSDoc "mimer.components.open" 40 $ "  term = " <+> prettyTCM term
  typ <- getOpen $ compType <$> openComp
  reportSDoc "mimer.components.open" 40 $ "  typ  =" <+> prettyTCM typ
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

newComponent :: MonadFresh CompId m => [MetaId] -> Cost -> Maybe Name -> Nat -> Term -> Type -> m Component
newComponent metaIds cost mName pars term typ = fresh <&> \cId -> mkComponent cId metaIds cost mName pars term typ

newComponentQ :: MonadFresh CompId m => [MetaId] -> Cost -> QName -> Nat -> Term -> Type -> m Component
newComponentQ metaIds cost qname pars term typ = fresh <&> \cId -> mkComponent cId metaIds cost (Just $ qnameName qname) pars term typ

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

-- | NOTE: Collects components from the *current* context, not the context of
-- the 'InteractionId'.
collectComponents :: Options
                  -> Costs
                  -> InteractionId
                  -> Maybe QName
                  -> [QName]
                  -> MetaId
                  -> TCM BaseComponents
collectComponents opts costs ii mDefName whereNames metaId = do

  lhsVars <- collectLHSVars ii
  let recVars = lhsVars <&> \ vars -> [ (tm, NoSubst i) | (tm, Just i) <- vars ]

  -- Prepare the initial component record
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
        }

  -- Extract additional components from the names given as hints.
  hintNames <- getEverythingInScope <$> lookupLocalMeta metaId
  isToLevel <- endsInLevelTester
  scope <- getScope
  components' <- foldM (go isToLevel scope) components $
    explicitHints ++ (hintNames List.\\ explicitHints)

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
    }
  where
    hintMode = optHintMode opts
    explicitHints = optExplicitHints opts
    -- Sort by the arity of the type
    doSort = List.sortOn (arity . compType)

    isNotMutual qname f = case mDefName of
      Nothing -> True
      Just defName -> defName /= qname && fmap (defName `elem`) (funMutual f) /= Just True

    go isToLevel scope comps qname = do
        def <- getConstInfo qname
        let typ = defType def
        case theDef def of
          Axiom{}
            | isToLevel typ -> addLevel
            | shouldKeep    -> addAxiom
            | otherwise     -> done
          -- We can't use pattern lambdas as components nor with-functions.
          -- If the function is in the same mutual block, do not include it.
          f@Function{ funWith = Nothing, funExtLam = Nothing }
            | Just qname == mDefName   -> addThisFn
            | notMutual, isToLevel typ -> addLevel
            | notMutual, shouldKeep    -> addFn
            where notMutual = isNotMutual qname f
          Function{} -> done
          Datatype{} -> addData
          Record{} -> do
            projections <- mapM (qnameToComponent (costSpeculateProj costs)) =<< getRecordFields qname
            comp <- qnameToComponent (costSet costs) qname
            return comps{ hintRecordTypes = comp : hintRecordTypes comps
                        , hintProjections = projections ++ hintProjections comps }
          -- We look up constructors when we need them
          Constructor{} -> done
          -- TODO: special treatment for primitives?
          Primitive{}
            | isToLevel typ  -> addLevel
            | shouldKeep     -> addFn
            | otherwise      -> done
          PrimitiveSort{}    -> done
          -- TODO: Check if we want to use these
          DataOrRecSig{}     -> done
          GeneralizableVar{} -> done
          AbstractDefn{}     -> done
        where
          done = return comps
          -- TODO: There is probably a better way of finding the module name
          mThisModule = qnameModule <$> mDefName

          shouldKeep = or
            [ qname `elem` explicitHints
            , qname `elem` whereNames
            , case hintMode of
                Unqualified -> Scope.isNameInScopeUnqualified qname scope
                AllModules  -> True
                Module      -> Just (qnameModule qname) == mThisModule
                NoHints     -> False
            ]
          addLevel  = qnameToComponent (costLevel   costs) qname <&> \ comp -> comps{hintLevel     = comp : hintLevel  comps}
          addAxiom  = qnameToComponent (costAxiom   costs) qname <&> \ comp -> comps{hintAxioms    = comp : hintAxioms comps}
          addThisFn = qnameToComponent (costRecCall costs) qname <&> \ comp -> comps{hintThisFn    = Just comp{ compRec = True }}
          addFn     = qnameToComponent (costFn      costs) qname <&> \ comp -> comps{hintFns       = comp : hintFns comps}
          addData   = qnameToComponent (costSet     costs) qname <&> \ comp -> comps{hintDataTypes = comp : hintDataTypes comps}


qnameToComponent :: (HasConstInfo tcm, ReadTCState tcm, MonadFresh CompId tcm, MonadTCM tcm)
  => Cost -> QName -> tcm Component
qnameToComponent cost qname = do
  defn <- getConstInfo qname
  -- #7120: we need to apply the module params to everything
  mParams <- freeVarsToApply qname
  let def = (Def qname [] `apply` mParams, 0)
  let (term, pars) = case theDef defn of
        c@Constructor{}    -> (Con (conSrcCon c) ConOCon [], conPars c - length mParams)
        Axiom{}            -> def
        GeneralizableVar{} -> def
        Function{}         -> def
        Datatype{}         -> def
        Record{}           -> def
        Primitive{}        -> def
        PrimitiveSort{}    -> def
        DataOrRecSig{}     -> __IMPOSSIBLE__
        AbstractDefn{}     -> __IMPOSSIBLE__
  newComponentQ [] cost qname pars term (defType defn `piApply` mParams)

-- | Turn the let bindings of the current 'TCEnv' into components.
getLetVars :: forall tcm. (MonadFresh CompId tcm, MonadTCM tcm, Monad tcm) => Cost -> tcm [Open Component]
getLetVars cost = do
  bindings <- asksTC envLetBindings
  mapM makeComp $ Map.toAscList bindings
  where
    makeComp :: (Name, Open LetBinding) -> tcm (Open Component)
    makeComp (name, opn) = do
      cId <- fresh
      return $ opn <&> \ (LetBinding _origin term typ) ->
                mkComponent cId [] cost (Just name) 0 term (unDom typ)

-- | Returns the variables as terms together with whether they where found under
-- some constructor, and if so which argument of the function they appeared in. This
-- information is used when building recursive calls, where it's important that we don't try to
-- construct non-terminating solutions.
collectLHSVars :: (ReadTCState tcm, MonadError TCErr tcm, MonadTCM tcm, HasConstInfo tcm)
  => InteractionId -> tcm (Open [(Term, Maybe Int)])
collectLHSVars ii = do
  ipc <- ipClause <$> lookupInteractionPoint ii
  case ipc of
    IPNoClause -> makeOpen []
    IPClause{ipcQName = fnName, ipcClauseNo = clauseNr} -> do
      reportSDoc "mimer.components" 40 $ "Collecting LHS vars for" <+> prettyTCM ii
      info <- getConstInfo fnName
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

applyProj :: Args -> Component -> QName -> SM Component
applyProj recordArgs comp' qname = do
  cost <- asks (costProj . searchCosts)
  -- Andreas, 2025-03-31, issue #7662: hack to prevent postfix printing of ♭
  projOrigin <- maybe ProjSystem (\ flat -> if qname == flat then ProjPrefix else ProjSystem)
    <$> asks searchBuiltinFlat
  let newTerm = applyE (compTerm comp') [Proj projOrigin qname]
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
  reportSDoc "mimer.component" 25 $ "Applying component to metas" <+> prettyTCM (compId comp) <+> prettyTCM (compTerm comp)
  ctx <- getContextTelescope
  compTyp <- reduce $ compType comp
  case unEl compTyp of
    Pi dom abs -> do
      let domainType = unDom dom
      (metaId, metaTerm) <- createMeta domainType
      reportSDoc "mimer.component" 30 $ "New arg meta" <+> prettyTCM metaTerm
      let arg = setOrigin Inserted $ metaTerm <$ argFromDom dom
      newType <- reduce =<< piApplyM (compType comp) metaTerm
      -- Constructor parameters are not included in the term
      let skip = compPars comp
          newTerm | skip > 0  = compTerm comp
                  | otherwise = apply (compTerm comp) [arg]
      cost <- asks $ (if getHiding arg == Hidden then costNewHiddenMeta else costNewMeta) . searchCosts
      let predNat n | n > 0     = n - 1
                    | n == 0    = 0
                    | otherwise = __IMPOSSIBLE__
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

------------------------------------------------------------------------
-- * Search branches
------------------------------------------------------------------------

withBranchState :: SearchBranch -> SM a -> SM a
withBranchState br ma = do
  putTC (sbTCState br)
  ma

withBranchAndGoal :: SearchBranch -> Goal -> SM a -> SM a
withBranchAndGoal br goal ma = inGoalEnv goal $ withBranchState br ma

inGoalEnv :: Goal -> SM a -> SM a
inGoalEnv goal  ret = do
  reportSDoc "mimer.env" 70 $ "going into environment of goal" <+> prettyTCM (goalMeta goal)
  withMetaId (goalMeta goal) ret

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

checkSolved :: SearchBranch -> SM SearchStepResult
checkSolved branch = do
  reportSDoc "mimer" 20 $ "Checking if branch is solved"
  reportSDoc "mimer" 30 $ "  remaining subgoals: " <+> prettyTCM (map goalMeta $ sbGoals branch)
  topMetaId <- asks searchTopMeta
  topMeta <- lookupLocalMeta topMetaId
  ii <- asks searchInteractionId
  withInteractionId ii $ withBranchState branch $ do
    metaArgs <- getMetaContextArgs topMeta
    inst <- normaliseSolution $ apply (MetaV topMetaId []) metaArgs
    -- Issue #7639: The subgoals as generated by `applyToMetasG` (and other functions)
    -- are already stored in the `sbGoals` field of the branch.
    -- Here we just prune the subgoals that are already solved by unification.
    goals <- filterM (isNothing <.> getMetaInstantiation . goalMeta) $ sbGoals branch
    case goals of
      -- Issue #378: Blank out variables that are not in scope.
      -- This might leave unsolved metas but is probably better
      -- than generating out-of-scope variables.
      [] -> ResultExpr <$> (blankNotInScope =<< reify inst)
      _ -> do
        return $ OpenBranch branch { sbGoals = goals }

normaliseSolution :: Term -> SM Term
normaliseSolution t = do
  norm <- asks searchRewrite
  lift . normalForm norm =<< instantiateFull t

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

------------------------------------------------------------------------
-- * Unification
------------------------------------------------------------------------

dumbUnifier :: Type -> Type -> SM Bool
dumbUnifier t1 t2 = isNothing <$> dumbUnifierErr t1 t2

dumbUnifierErr :: Type -> Type -> SM (Maybe TCErr)
dumbUnifierErr t1 t2 = bench [Bench.UnifyIndices] $ do
  updateStat incTypeEqChecks
  noConstraints (Nothing <$ equalType t2 t1) `catchError` \err -> do
    reportSDoc "mimer.unify" 80 $ sep [ "Unification failed with error:", nest 2 $ prettyTCM err ]
    return $ Just err

------------------------------------------------------------------------
-- * Debugging
------------------------------------------------------------------------

reportSMDoc :: VerboseKey -> VerboseLevel -> SM Doc -> SM ()
reportSMDoc vk vl md = reportSDoc vk vl . runReaderT md =<< ask

mimerTrace :: Int -> VerboseLevel -> SM Doc -> SM ()
mimerTrace ilvl vlvl doc = reportSMDoc "mimer.trace" vlvl $ nest (2 * ilvl) $ "-" <+> doc

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

------------------------------------------------------------------------
-- * Stats
------------------------------------------------------------------------

updateStat :: (MimerStats -> MimerStats) -> SM ()
updateStat f = verboseS "mimer.stats" 10 $ do
  ref <- asks searchStats
  liftIO $ modifyIORef' ref f

bench :: NFData a => [Bench.Phase] -> SM a -> SM a
bench k ma = billTo (mimerAccount : k) ma
  where
    -- Dummy account to avoid updating Bench. Doesn't matter since this is only used interactively
    -- to debug Mimer performance.
    mimerAccount = Bench.Sort

writeTime :: (ReadTCState m, MonadError TCErr m, MonadTCM m, MonadDebug m) => InteractionId -> Maybe CPUTime -> m ()
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

