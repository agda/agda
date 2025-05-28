
module Agda.Mimer.Monad where

import Control.DeepSeq (NFData(..))
import Control.Monad
import Control.Monad.Except (catchError)
import Control.Monad.IO.Class (liftIO)
import Control.Monad.Reader (ReaderT(..), asks, ask)
import Data.IORef (modifyIORef')
import Data.Map qualified as Map
import Data.List qualified as List
import Data.Maybe

import Agda.Syntax.Common (MetaId, Nat)
import Agda.Syntax.Concrete.Name qualified as C
import Agda.Syntax.Internal (Term(..), Type, QName(..), Name, Dom, Dom'(..))
import Agda.Syntax.Internal.MetaVars (AllMetas(..))
import Agda.Syntax.Translation.AbstractToConcrete (abstractToConcrete_)
import Agda.TypeChecking.Monad
import Agda.TypeChecking.Pretty
import Agda.TypeChecking.Conversion (equalType)
import Agda.TypeChecking.Constraints (noConstraints)
import Agda.TypeChecking.Telescope (flattenTel)
import Agda.Benchmarking qualified as Bench
import Agda.Utils.Benchmark (billTo)
import Agda.Utils.Functor ((<&>))
import Agda.Utils.Impossible

import Agda.Mimer.Types

type SM a = ReaderT SearchOptions TCM a

------------------------------------------------------------------------
-- * Agda internals
------------------------------------------------------------------------

getRecordFields :: (HasConstInfo tcm, MonadTCM tcm) => QName -> tcm [QName]
getRecordFields = fmap (map unDom . recFields . theDef) . getConstInfo

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

------------------------------------------------------------------------
-- * Components
------------------------------------------------------------------------

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

------------------------------------------------------------------------
-- * Search branches
------------------------------------------------------------------------

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

