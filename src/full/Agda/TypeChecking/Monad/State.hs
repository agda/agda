-- | Lenses for 'TCState' and more.

module Agda.TypeChecking.Monad.State where


import qualified Control.Exception as E

import Control.Monad       (void, when)
import Control.Monad.Trans (MonadIO, liftIO)

import Data.Maybe

import qualified Data.Map as Map

import Data.Set (Set)
import qualified Data.Set as Set
import qualified Data.HashMap.Strict as HMap

import Agda.Benchmarking

import Agda.Interaction.Response
  (InteractionOutputCallback, Response)

import Agda.Syntax.Common
import Agda.Syntax.Scope.Base
import qualified Agda.Syntax.Concrete.Name as C
import Agda.Syntax.Abstract (PatternSynDefn, PatternSynDefns)
import Agda.Syntax.Abstract.PatternSynonyms
import Agda.Syntax.Abstract.Name
import Agda.Syntax.Internal
import Agda.Syntax.Position
import Agda.Syntax.TopLevelModuleName

import Agda.TypeChecking.Monad.Base
import Agda.TypeChecking.Warnings

import Agda.TypeChecking.Monad.Debug (reportSDoc, reportSLn, verboseS)
import Agda.TypeChecking.Positivity.Occurrence
import Agda.TypeChecking.CompiledClause

import qualified Agda.Utils.BiMap as BiMap
import Agda.Utils.Hash
import Agda.Utils.Lens
import qualified Agda.Utils.List1 as List1
import Agda.Utils.Monad (bracket_)
import Agda.Utils.Pretty
import Agda.Utils.Tuple

import Agda.Utils.Impossible

-- | Resets the non-persistent part of the type checking state.

resetState :: TCM ()
resetState = do
    pers <- getsTC stPersistentState
    putTC $ initState { stPersistentState = pers }

-- | Resets all of the type checking state.
--
--   Keep only 'Benchmark' and backend information.

resetAllState :: TCM ()
resetAllState = do
    b <- getBenchmark
    backends <- useTC stBackends
    putTC $ updatePersistentState (\ s -> s { stBenchmark = b }) initState
    stBackends `setTCLens` backends
-- resetAllState = putTC initState

-- | Restore 'TCState' after performing subcomputation.
--
--   In contrast to 'Agda.Utils.Monad.localState', the 'Benchmark'
--   info from the subcomputation is saved.
localTCState :: TCM a -> TCM a
localTCState = bracket_ getTC (\ s -> do
   b <- getBenchmark
   putTC s
   modifyBenchmark $ const b)

-- | Same as 'localTCState' but also returns the state in which we were just
--   before reverting it.
localTCStateSaving :: TCM a -> TCM (a, TCState)
localTCStateSaving compute = do
  oldState <- getTC
  result <- compute
  newState <- getTC
  do
    b <- getBenchmark
    putTC oldState
    modifyBenchmark $ const b
  return (result, newState)

-- | Same as 'localTCState' but keep all warnings.
localTCStateSavingWarnings :: TCM a -> TCM a
localTCStateSavingWarnings compute = do
  (result, newState) <- localTCStateSaving compute
  modifyTC $ over stTCWarnings $ const $ newState ^. stTCWarnings
  return result

data SpeculateResult = SpeculateAbort | SpeculateCommit

-- | Allow rolling back the state changes of a TCM computation.
speculateTCState :: TCM (a, SpeculateResult) -> TCM a
speculateTCState m = do
  ((x, res), newState) <- localTCStateSaving m
  case res of
    SpeculateAbort  -> return x
    SpeculateCommit -> x <$ putTC newState

speculateTCState_ :: TCM SpeculateResult -> TCM ()
speculateTCState_ m = void $ speculateTCState $ ((),) <$> m

-- | A fresh TCM instance.
--
-- The computation is run in a fresh state, with the exception that
-- the persistent state is preserved. If the computation changes the
-- state, then these changes are ignored, except for changes to the
-- persistent state. (Changes to the persistent state are also ignored
-- if errors other than type errors or IO exceptions are encountered.)

freshTCM :: TCM a -> TCM (Either TCErr a)
freshTCM m = do
  ps <- useTC lensPersistentState
  let s = set lensPersistentState ps initState
  r <- liftIO $ (Right <$> runTCM initEnv s m) `E.catch` (return . Left)
  case r of
    Right (a, s) -> do
      setTCLens lensPersistentState $ s ^. lensPersistentState
      return $ Right a
    Left err -> do
      case err of
        TypeError { tcErrState = s } ->
          setTCLens lensPersistentState $ s ^. lensPersistentState
        IOException s _ _ ->
          setTCLens lensPersistentState $ s ^. lensPersistentState
        _ -> return ()
      return $ Left err

---------------------------------------------------------------------------
-- * Lens for persistent states and its fields
---------------------------------------------------------------------------

lensPersistentState :: Lens' TCState PersistentTCState
lensPersistentState f s =
  f (stPersistentState s) <&> \ p -> s { stPersistentState = p }

updatePersistentState
  :: (PersistentTCState -> PersistentTCState) -> (TCState -> TCState)
updatePersistentState f s = s { stPersistentState = f (stPersistentState s) }

modifyPersistentState :: (PersistentTCState -> PersistentTCState) -> TCM ()
modifyPersistentState = modifyTC . updatePersistentState

-- | Lens for 'stAccumStatistics'.

lensAccumStatisticsP :: Lens' PersistentTCState Statistics
lensAccumStatisticsP f s = f (stAccumStatistics s) <&> \ a ->
  s { stAccumStatistics = a }

lensAccumStatistics :: Lens' TCState Statistics
lensAccumStatistics =  lensPersistentState . lensAccumStatisticsP

---------------------------------------------------------------------------
-- * Scope
---------------------------------------------------------------------------

-- | Get the current scope.
getScope :: ReadTCState m => m ScopeInfo
getScope = useR stScope

-- | Set the current scope.
setScope :: ScopeInfo -> TCM ()
setScope scope = modifyScope (const scope)

-- | Modify the current scope without updating the inverse maps.
modifyScope_ :: MonadTCState m => (ScopeInfo -> ScopeInfo) -> m ()
modifyScope_ f = stScope `modifyTCLens` f

-- | Modify the current scope.
modifyScope :: MonadTCState m => (ScopeInfo -> ScopeInfo) -> m ()
modifyScope f = modifyScope_ (recomputeInverseScopeMaps . f)

-- | Get a part of the current scope.
useScope :: ReadTCState m => Lens' ScopeInfo a -> m a
useScope l = useR $ stScope . l

-- | Run a computation in a modified scope.
locallyScope :: ReadTCState m => Lens' ScopeInfo a -> (a -> a) -> m b -> m b
locallyScope l = locallyTCState $ stScope . l

-- | Run a computation in a local scope.
withScope :: ReadTCState m => ScopeInfo -> m a -> m (a, ScopeInfo)
withScope s m = locallyTCState stScope (recomputeInverseScopeMaps . const s) $ (,) <$> m <*> getScope

-- | Same as 'withScope', but discard the scope from the computation.
withScope_ :: ReadTCState m => ScopeInfo -> m a -> m a
withScope_ s m = fst <$> withScope s m

-- | Discard any changes to the scope by a computation.
localScope :: TCM a -> TCM a
localScope m = do
  scope <- getScope
  x <- m
  setScope scope
  return x

-- | Scope error.
notInScopeError :: C.QName -> TCM a
notInScopeError x = do
  printScope "unbound" 5 ""
  typeError $ NotInScope [x]

notInScopeWarning :: C.QName -> TCM ()
notInScopeWarning x = do
  printScope "unbound" 5 ""
  warning $ NotInScopeW [x]

-- | Debug print the scope.
printScope :: String -> Int -> String -> TCM ()
printScope tag v s = verboseS ("scope." ++ tag) v $ do
  scope <- getScope
  reportSDoc ("scope." ++ tag) v $ return $ vcat [ text s, pretty scope ]

---------------------------------------------------------------------------
-- * Signature
---------------------------------------------------------------------------

-- ** Lens for 'stSignature' and 'stImports'

modifySignature :: MonadTCState m => (Signature -> Signature) -> m ()
modifySignature f = stSignature `modifyTCLens` f

modifyImportedSignature :: MonadTCState m => (Signature -> Signature) -> m ()
modifyImportedSignature f = stImports `modifyTCLens` f

getSignature :: ReadTCState m => m Signature
getSignature = useR stSignature

-- | Update a possibly imported definition. Warning: changes made to imported
--   definitions (during type checking) will not persist outside the current
--   module. This function is currently used to update the compiled
--   representation of a function during compilation.
modifyGlobalDefinition :: MonadTCState m => QName -> (Definition -> Definition) -> m ()
modifyGlobalDefinition q f = do
  modifySignature         $ updateDefinition q f
  modifyImportedSignature $ updateDefinition q f

setSignature :: MonadTCState m => Signature -> m ()
setSignature sig = modifySignature $ const sig

-- | Run some computation in a different signature, restore original signature.
withSignature :: (ReadTCState m, MonadTCState m) => Signature -> m a -> m a
withSignature sig m = do
  sig0 <- getSignature
  setSignature sig
  r <- m
  setSignature sig0
  return r

-- ** Modifiers for rewrite rules
addRewriteRulesFor :: QName -> RewriteRules -> [QName] -> Signature -> Signature
addRewriteRulesFor f rews matchables =
    over sigRewriteRules (HMap.insertWith mappend f rews)
  . updateDefinition f (updateTheDef setNotInjective . setCopatternLHS)
  . (setMatchableSymbols f matchables)
    where
      setNotInjective def@Function{} = def { funInv = NotInjective }
      setNotInjective def            = def

      setCopatternLHS =
        updateDefCopatternLHS (|| any hasProjectionPattern rews)

      hasProjectionPattern rew = any (isJust . isProjElim) $ rewPats rew

setMatchableSymbols :: QName -> [QName] -> Signature -> Signature
setMatchableSymbols f matchables =
  foldr ((.) . (\g -> updateDefinition g setMatchable)) id matchables
    where
      setMatchable def = def { defMatchable = Set.insert f $ defMatchable def }

-- ** Modifiers for parts of the signature

lookupDefinition :: QName -> Signature -> Maybe Definition
lookupDefinition q sig = HMap.lookup q $ sig ^. sigDefinitions

updateDefinitions :: (Definitions -> Definitions) -> Signature -> Signature
updateDefinitions = over sigDefinitions

updateDefinition :: QName -> (Definition -> Definition) -> Signature -> Signature
updateDefinition q f = updateDefinitions $ HMap.adjust f q

updateTheDef :: (Defn -> Defn) -> (Definition -> Definition)
updateTheDef f def = def { theDef = f (theDef def) }

updateDefType :: (Type -> Type) -> (Definition -> Definition)
updateDefType f def = def { defType = f (defType def) }

updateDefArgOccurrences :: ([Occurrence] -> [Occurrence]) -> (Definition -> Definition)
updateDefArgOccurrences f def = def { defArgOccurrences = f (defArgOccurrences def) }

updateDefPolarity :: ([Polarity] -> [Polarity]) -> (Definition -> Definition)
updateDefPolarity f def = def { defPolarity = f (defPolarity def) }

updateDefCompiledRep :: (CompiledRepresentation -> CompiledRepresentation) -> (Definition -> Definition)
updateDefCompiledRep f def = def { defCompiledRep = f (defCompiledRep def) }

addCompilerPragma :: BackendName -> CompilerPragma -> Definition -> Definition
addCompilerPragma backend pragma = updateDefCompiledRep $ Map.insertWith (++) backend [pragma]

updateFunClauses :: ([Clause] -> [Clause]) -> (Defn -> Defn)
updateFunClauses f def@Function{ funClauses = cs} = def { funClauses = f cs }
updateFunClauses f _                              = __IMPOSSIBLE__

updateCovering :: ([Clause] -> [Clause]) -> (Defn -> Defn)
updateCovering f def@Function{ funCovering = cs} = def { funCovering = f cs }
updateCovering f _                               = __IMPOSSIBLE__

updateCompiledClauses :: (Maybe CompiledClauses -> Maybe CompiledClauses) -> (Defn -> Defn)
updateCompiledClauses f def@Function{ funCompiled = cc} = def { funCompiled = f cc }
updateCompiledClauses f _                              = __IMPOSSIBLE__

updateDefCopatternLHS :: (Bool -> Bool) -> Definition -> Definition
updateDefCopatternLHS f def@Defn{ defCopatternLHS = b } = def { defCopatternLHS = f b }

updateDefBlocked :: (Blocked_ -> Blocked_) -> Definition -> Definition
updateDefBlocked f def@Defn{ defBlocked = b } = def { defBlocked = f b }

---------------------------------------------------------------------------
-- * Top level module
---------------------------------------------------------------------------

-- | Tries to convert a raw top-level module name to a top-level
-- module name.

topLevelModuleName :: RawTopLevelModuleName -> TCM TopLevelModuleName
topLevelModuleName raw = do
  hash <- BiMap.lookup raw <$> useR stTopLevelModuleNames
  case hash of
    Just hash -> return (unsafeTopLevelModuleName raw hash)
    Nothing   -> do
      let hash = hashRawTopLevelModuleName raw
      when (hash == noModuleNameHash) $ typeError $ GenericError $
        "The module name " ++ prettyShow raw ++ " has a reserved " ++
        "hash (you may want to consider renaming the module with " ++
        "this name)"
      raw' <- BiMap.invLookup hash <$> useR stTopLevelModuleNames
      case raw' of
        Just raw' -> typeError $ GenericError $
          "Module name hash collision for " ++ prettyShow raw ++
          " and " ++ prettyShow raw' ++ " (you may want to consider " ++
          "renaming one of these modules)"
        Nothing -> do
          stTopLevelModuleNames `modifyTCLens'`
            BiMap.insert (killRange raw) hash
          return (unsafeTopLevelModuleName raw hash)

-- | Set the top-level module. This affects the global module id of freshly
--   generated names.

setTopLevelModule :: TopLevelModuleName -> TCM ()
setTopLevelModule top = do
  let hash = moduleNameId top
  stFreshNameId `setTCLens'` NameId 0 hash
  stFreshOpaqueId `setTCLens'` OpaqueId 0 hash
  stFreshMetaId `setTCLens'`
    MetaId { metaId     = 0
           , metaModule = hash
           }

-- | The name of the current top-level module, if any.
{-# SPECIALIZE
    currentTopLevelModule :: TCM (Maybe TopLevelModuleName) #-}
{-# SPECIALIZE
    currentTopLevelModule :: ReduceM (Maybe TopLevelModuleName) #-}
currentTopLevelModule ::
  (MonadTCEnv m, ReadTCState m) => m (Maybe TopLevelModuleName)
currentTopLevelModule = do
  m <- useR stCurrentModule
  case m of
    Just (_, top) -> return (Just top)
    Nothing       -> do
      p <- asksTC envImportPath
      return $ case p of
        top : _ -> Just top
        []      -> Nothing

-- | Use a different top-level module for a computation. Used when generating
--   names for imported modules.
withTopLevelModule :: TopLevelModuleName -> TCM a -> TCM a
withTopLevelModule x m = do
  nextN <- useTC stFreshNameId
  nextM <- useTC stFreshMetaId
  nextO <- useTC stFreshOpaqueId
  setTopLevelModule x
  y <- m
  stFreshMetaId `setTCLens` nextM
  stFreshNameId `setTCLens` nextN
  stFreshOpaqueId `setTCLens` nextO
  return y

currentModuleNameHash :: ReadTCState m => m ModuleNameHash
currentModuleNameHash = do
  NameId _ h <- useTC stFreshNameId
  return h

---------------------------------------------------------------------------
-- * Foreign code
---------------------------------------------------------------------------

addForeignCode :: BackendName -> String -> TCM ()
addForeignCode backend code = do
  r <- asksTC envRange  -- can't use TypeChecking.Monad.Trace.getCurrentRange without cycle
  modifyTCLens (stForeignCode . key backend) $
    Just . ForeignCodeStack . (ForeignCode r code :) . maybe [] getForeignCodeStack

---------------------------------------------------------------------------
-- * Interaction output callback
---------------------------------------------------------------------------

getInteractionOutputCallback :: ReadTCState m => m InteractionOutputCallback
getInteractionOutputCallback
  = getsTC $ stInteractionOutputCallback . stPersistentState

appInteractionOutputCallback :: Response -> TCM ()
appInteractionOutputCallback r
  = getInteractionOutputCallback >>= \ cb -> cb r

setInteractionOutputCallback :: InteractionOutputCallback -> TCM ()
setInteractionOutputCallback cb
  = modifyPersistentState $ \ s -> s { stInteractionOutputCallback = cb }

---------------------------------------------------------------------------
-- * Pattern synonyms
---------------------------------------------------------------------------

getPatternSyns :: ReadTCState m => m PatternSynDefns
getPatternSyns = useR stPatternSyns

setPatternSyns :: PatternSynDefns -> TCM ()
setPatternSyns m = modifyPatternSyns (const m)

-- | Lens for 'stPatternSyns'.
modifyPatternSyns :: (PatternSynDefns -> PatternSynDefns) -> TCM ()
modifyPatternSyns f = stPatternSyns `modifyTCLens` f

getPatternSynImports :: ReadTCState m => m PatternSynDefns
getPatternSynImports = useR stPatternSynImports

-- | Get both local and imported pattern synonyms
getAllPatternSyns :: ReadTCState m => m PatternSynDefns
getAllPatternSyns = Map.union <$> getPatternSyns <*> getPatternSynImports

lookupPatternSyn :: AmbiguousQName -> TCM PatternSynDefn
lookupPatternSyn (AmbQ xs) = do
  defs <- traverse lookupSinglePatternSyn xs
  case mergePatternSynDefs defs of
    Just def   -> return def
    Nothing    -> typeError $ CannotResolveAmbiguousPatternSynonym $ List1.zip xs defs

lookupSinglePatternSyn :: QName -> TCM PatternSynDefn
lookupSinglePatternSyn x = do
    s <- getPatternSyns
    case Map.lookup x s of
        Just d  -> return d
        Nothing -> do
            si <- getPatternSynImports
            case Map.lookup x si of
                Just d  -> return d
                Nothing -> notInScopeError $ qnameToConcrete x

---------------------------------------------------------------------------
-- * Benchmark
---------------------------------------------------------------------------

-- | Lens getter for 'Benchmark' from 'TCState'.
theBenchmark :: TCState -> Benchmark
theBenchmark = stBenchmark . stPersistentState

-- | Lens map for 'Benchmark'.
updateBenchmark :: (Benchmark -> Benchmark) -> TCState -> TCState
updateBenchmark f = updatePersistentState $ \ s -> s { stBenchmark = f (stBenchmark s) }

-- | Lens getter for 'Benchmark' from 'TCM'.
getBenchmark :: TCM Benchmark
getBenchmark = getsTC $ theBenchmark

-- | Lens modify for 'Benchmark'.
modifyBenchmark :: (Benchmark -> Benchmark) -> TCM ()
modifyBenchmark = modifyTC' . updateBenchmark

---------------------------------------------------------------------------
-- * Instance definitions
---------------------------------------------------------------------------

-- | Look through the signature and reconstruct the instance table.
addImportedInstances :: Signature -> TCM ()
addImportedInstances sig = do
  let itable = Map.fromListWith Set.union
               [ (c, Set.singleton i)
               | (i, Defn{ defInstance = Just c }) <- HMap.toList $ sig ^. sigDefinitions ]
  stImportedInstanceDefs `modifyTCLens` Map.unionWith Set.union itable

-- | Lens for 'stInstanceDefs'.
updateInstanceDefs :: (TempInstanceTable -> TempInstanceTable) -> (TCState -> TCState)
updateInstanceDefs = over stInstanceDefs

modifyInstanceDefs :: (TempInstanceTable -> TempInstanceTable) -> TCM ()
modifyInstanceDefs = modifyTC . updateInstanceDefs

getAllInstanceDefs :: TCM TempInstanceTable
getAllInstanceDefs = do
  (table,xs) <- useTC stInstanceDefs
  itable <- useTC stImportedInstanceDefs
  let !table' = Map.unionWith Set.union itable table
  return (table', xs)

getAnonInstanceDefs :: TCM (Set QName)
getAnonInstanceDefs = snd <$> getAllInstanceDefs

-- | Remove all instances whose type is still unresolved.
clearAnonInstanceDefs :: TCM ()
clearAnonInstanceDefs = modifyInstanceDefs $ mapSnd $ const Set.empty

-- | Add an instance whose type is still unresolved.
addUnknownInstance :: QName -> TCM ()
addUnknownInstance x = do
  reportSLn "tc.decl.instance" 10 $
    "adding definition " ++ prettyShow x ++
    " to the instance table (the type is not yet known)"
  modifyInstanceDefs $ mapSnd $ Set.insert x

-- | Add instance to some ``class''.
addNamedInstance
  :: QName  -- ^ Name of the instance.
  -> QName  -- ^ Name of the class.
  -> TCM ()
addNamedInstance x n = do
  reportSLn "tc.decl.instance" 10 $
    "adding definition " ++ prettyShow x ++ " to instance table for " ++ prettyShow n
  -- Mark x as instance for n.
  modifySignature $ updateDefinition x $ \ d -> d { defInstance = Just n }
  -- Add x to n's instances.
  modifyInstanceDefs $ mapFst $ Map.insertWith Set.union n $ Set.singleton x
