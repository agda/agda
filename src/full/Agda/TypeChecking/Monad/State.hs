{-# LANGUAGE CPP #-}

-- | Lenses for 'TCState' and more.

module Agda.TypeChecking.Monad.State where

import Control.Arrow (first)
import Control.Applicative
import qualified Control.Exception as E
import Control.Monad.State (put, get, gets, modify)
import Control.Monad.Trans (liftIO)

import Data.Map as Map
import Data.Monoid
import Data.Set (Set)
import qualified Data.Set as Set

import Agda.Benchmarking

-- import {-# SOURCE #-} Agda.Interaction.Response
import Agda.Interaction.Response
  (InteractionOutputCallback, Response)

import Agda.Syntax.Common
import Agda.Syntax.Scope.Base
import qualified Agda.Syntax.Concrete.Name as C
import Agda.Syntax.Abstract (PatternSynDefn, PatternSynDefns)
import Agda.Syntax.Abstract.Name
import Agda.Syntax.Internal

import Agda.TypeChecking.Monad.Base
import {-# SOURCE #-} Agda.TypeChecking.Monad.Options
import Agda.TypeChecking.Positivity.Occurrence

import Agda.Utils.Hash
import qualified Agda.Utils.HashMap as HMap
import Agda.Utils.Lens
import Agda.Utils.Monad (bracket_, modify')
import Agda.Utils.Pretty
import Agda.Utils.Tuple

#include "undefined.h"
import Agda.Utils.Impossible

-- | Resets the non-persistent part of the type checking state.

resetState :: TCM ()
resetState = do
    pers <- gets stPersistentState
    put $ initState { stPersistentState = pers }

-- | Resets all of the type checking state.
--
--   Keep only 'Benchmark' information.

resetAllState :: TCM ()
resetAllState = do
    b <- getBenchmark
    put $ updatePersistentState (\ s -> s { stBenchmark = b }) initState
-- resetAllState = put initState

-- | Restore 'TCState' after performing subcomputation.
--
--   In contrast to 'Agda.Utils.Monad.localState', the 'Benchmark'
--   info from the subcomputation is saved.
localTCState :: TCM a -> TCM a
localTCState = disableDestructiveUpdate . bracket_ get (\ s -> do
   b <- getBenchmark
   put s
   modifyBenchmark $ const b)

-- | Same as 'localTCState' but also returns the state in which we were just
--   before reverting it.
localTCStateSaving :: TCM a -> TCM (a, TCState)
localTCStateSaving compute = do
  oldState <- get
  result <- compute
  newState <- get
  do
    b <- getBenchmark
    put oldState
    modifyBenchmark $ const b
  return (result, newState)


---------------------------------------------------------------------------
-- * Lens for persistent states and its fields
---------------------------------------------------------------------------

lensPersistentState :: Lens' PersistentTCState TCState
lensPersistentState f s =
  f (stPersistentState s) <&> \ p -> s { stPersistentState = p }

updatePersistentState
  :: (PersistentTCState -> PersistentTCState) -> (TCState -> TCState)
updatePersistentState f s = s { stPersistentState = f (stPersistentState s) }

modifyPersistentState :: (PersistentTCState -> PersistentTCState) -> TCM ()
modifyPersistentState = modify . updatePersistentState

-- | Lens for 'stAccumStatistics'.

lensAccumStatisticsP :: Lens' Statistics PersistentTCState
lensAccumStatisticsP f s = f (stAccumStatistics s) <&> \ a ->
  s { stAccumStatistics = a }

lensAccumStatistics :: Lens' Statistics TCState
lensAccumStatistics =  lensPersistentState . lensAccumStatisticsP

---------------------------------------------------------------------------
-- * Scope
---------------------------------------------------------------------------

-- | Get the current scope.
getScope :: TCM ScopeInfo
getScope = use stScope

-- | Set the current scope.
setScope :: ScopeInfo -> TCM ()
setScope scope = modifyScope (const scope)

-- | Modify the current scope without updating the inverse maps.
modifyScope_ :: (ScopeInfo -> ScopeInfo) -> TCM ()
modifyScope_ f = stScope %= f

-- | Modify the current scope.
modifyScope :: (ScopeInfo -> ScopeInfo) -> TCM ()
modifyScope f = modifyScope_ (recomputeInverseScopeMaps . f)

-- | Run a computation in a local scope.
withScope :: ScopeInfo -> TCM a -> TCM (a, ScopeInfo)
withScope s m = do
  s' <- getScope
  setScope s
  x   <- m
  s'' <- getScope
  setScope s'
  return (x, s'')

-- | Same as 'withScope', but discard the scope from the computation.
withScope_ :: ScopeInfo -> TCM a -> TCM a
withScope_ s m = fst <$> withScope s m

-- | Discard any changes to the scope by a computation.
localScope :: TCM a -> TCM a
localScope m = do
  scope <- getScope
  x <- m
  setScope scope
  return x

-- | Scope error.
notInScope :: C.QName -> TCM a
notInScope x = do
  printScope "unbound" 5 ""
  typeError $ NotInScope [x]

-- | Debug print the scope.
printScope :: String -> Int -> String -> TCM ()
printScope tag v s = verboseS ("scope." ++ tag) v $ do
  scope <- getScope
  reportSDoc ("scope." ++ tag) v $ return $ vcat [ text s, text $ show scope ]

---------------------------------------------------------------------------
-- * Signature
---------------------------------------------------------------------------

-- ** Lens for 'stSignature' and 'stImports'

modifySignature :: (Signature -> Signature) -> TCM ()
modifySignature f = stSignature %= f

modifyImportedSignature :: (Signature -> Signature) -> TCM ()
modifyImportedSignature f = stImports %= f

getSignature :: TCM Signature
getSignature = use stSignature

getImportedSignature :: TCM Signature
getImportedSignature = use stImports

-- | Update a possibly imported definition. Warning: changes made to imported
--   definitions (during type checking) will not persist outside the current
--   module. This function is currently used to update the compiled
--   representation of a function during compilation.
modifyGlobalDefinition :: QName -> (Definition -> Definition) -> TCM ()
modifyGlobalDefinition q f = modifySignature (updateDefinition q f) >>
                             modifyImportedSignature (updateDefinition q f)

setSignature :: Signature -> TCM ()
setSignature sig = modifySignature $ const sig

setImportedSignature :: Signature -> TCM ()
setImportedSignature sig = stImports .= sig

-- | Run some computation in a different signature, restore original signature.
withSignature :: Signature -> TCM a -> TCM a
withSignature sig m = do
  sig0 <- getSignature
  setSignature sig
  r <- m
  setSignature sig0
  return r

-- ** Modifiers for rewrite rules
addRewriteRulesFor :: QName -> RewriteRules -> Signature -> Signature
addRewriteRulesFor f rews =
    (over sigRewriteRules $ HMap.insertWith mappend f rews)
  . (updateDefinition f $ updateTheDef setNotInjective)
    where
      setNotInjective def@Function{} = def { funInv = NotInjective }
      setNotInjective def            = def

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

updateFunClauses :: ([Clause] -> [Clause]) -> (Defn -> Defn)
updateFunClauses f def@Function{ funClauses = cs} = def { funClauses = f cs }
updateFunClauses f _                              = __IMPOSSIBLE__

---------------------------------------------------------------------------
-- * Top level module
---------------------------------------------------------------------------

-- | Set the top-level module. This affects the global module id of freshly
--   generated names.

-- TODO: Is the hash-function collision-free? If not, then the
-- implementation of 'setTopLevelModule' should be changed.

setTopLevelModule :: C.QName -> TCM ()
setTopLevelModule x = stFreshNameId .= NameId 0 (hashString (show x))

-- | Use a different top-level module for a computation. Used when generating
--   names for imported modules.
withTopLevelModule :: C.QName -> TCM a -> TCM a
withTopLevelModule x m = do
  next <- use stFreshNameId
  setTopLevelModule x
  y <- m
  stFreshNameId .= next
  return y

---------------------------------------------------------------------------
-- * Haskell imports
---------------------------------------------------------------------------

-- | Tell the compiler to import the given Haskell module.
addHaskellImport :: String -> TCM ()
addHaskellImport i = stHaskellImports %= Set.insert i

-- | Get the Haskell imports.
getHaskellImports :: TCM (Set String)
getHaskellImports = use stHaskellImports

-- | Tell the compiler to import the given Haskell module.
addHaskellImportUHC :: String -> TCM ()
addHaskellImportUHC i = stHaskellImportsUHC %= Set.insert i

-- | Get the Haskell imports.
getHaskellImportsUHC :: TCM (Set String)
getHaskellImportsUHC = use stHaskellImportsUHC

addInlineHaskell :: String -> TCM ()
addInlineHaskell s = stHaskellCode %= (s :)

---------------------------------------------------------------------------
-- * Interaction output callback
---------------------------------------------------------------------------

getInteractionOutputCallback :: TCM InteractionOutputCallback
getInteractionOutputCallback
  = gets $ stInteractionOutputCallback . stPersistentState

appInteractionOutputCallback :: Response -> TCM ()
appInteractionOutputCallback r
  = getInteractionOutputCallback >>= \ cb -> cb r

setInteractionOutputCallback :: InteractionOutputCallback -> TCM ()
setInteractionOutputCallback cb
  = modifyPersistentState $ \ s -> s { stInteractionOutputCallback = cb }

---------------------------------------------------------------------------
-- * Pattern synonyms
---------------------------------------------------------------------------

getPatternSyns :: TCM PatternSynDefns
getPatternSyns = use stPatternSyns

setPatternSyns :: PatternSynDefns -> TCM ()
setPatternSyns m = modifyPatternSyns (const m)

-- | Lens for 'stPatternSyns'.
modifyPatternSyns :: (PatternSynDefns -> PatternSynDefns) -> TCM ()
modifyPatternSyns f = stPatternSyns %= f

getPatternSynImports :: TCM PatternSynDefns
getPatternSynImports = use stPatternSynImports

lookupPatternSyn :: QName -> TCM PatternSynDefn
lookupPatternSyn x = do
    s <- getPatternSyns
    case Map.lookup x s of
        Just d  -> return d
        Nothing -> do
            si <- getPatternSynImports
            case Map.lookup x si of
                Just d  -> return d
                Nothing -> notInScope $ qnameToConcrete x

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
getBenchmark = gets $ theBenchmark

-- | Lens modify for 'Benchmark'.
modifyBenchmark :: (Benchmark -> Benchmark) -> TCM ()
modifyBenchmark = modify' . updateBenchmark

-- | Run a fresh instance of the TCM (with initial state).
--   'Benchmark' info is preserved.
freshTCM :: TCM a -> TCM (Either TCErr a)
freshTCM m = do
  -- Prepare an initial state with current benchmark info.
  b <- getBenchmark
  a <- use lensAccumStatistics
  let s = updateBenchmark (const b)
        . set lensAccumStatistics a
        $ initState
  -- Run subcomputation in initial state.
  -- If we encounter an exception, we lose the state and the
  -- benchmark info.
  -- We could retrieve i from a type error, which carries the state,
  -- but we do not care for benchmarking in the presence of errors.
  r <- liftIO $ (Right <$> runTCM initEnv s m) `E.catch` (return . Left)
  case r of
    Left err     -> return $ Left err
    Right (a, s) -> do
      -- Keep only the benchmark info from the final state of the subcomp.
      modifyBenchmark $ const $ theBenchmark s
      lensAccumStatistics .= (s^.lensAccumStatistics)
      return $ Right a

---------------------------------------------------------------------------
-- * Instance definitions
---------------------------------------------------------------------------

-- | Look through the signature and reconstruct the instance table.
addSignatureInstances :: Signature -> TCM ()
addSignatureInstances sig = do
  let itable = Map.fromListWith (++)
               [ (c, [i]) | (i, Defn{ defInstance = Just c }) <- HMap.toList $ sig ^. sigDefinitions ]
  modifyInstanceDefs $ first $ Map.unionWith (++) itable

-- | Lens for 'stInstanceDefs'.
updateInstanceDefs :: (TempInstanceTable -> TempInstanceTable) -> (TCState -> TCState)
updateInstanceDefs = over stInstanceDefs

modifyInstanceDefs :: (TempInstanceTable -> TempInstanceTable) -> TCM ()
modifyInstanceDefs = modify . updateInstanceDefs

getAllInstanceDefs :: TCM TempInstanceTable
getAllInstanceDefs = use stInstanceDefs

getAnonInstanceDefs :: TCM [QName]
getAnonInstanceDefs = snd <$> getAllInstanceDefs

-- | Remove all instances whose type is still unresolved.
clearAnonInstanceDefs :: TCM ()
clearAnonInstanceDefs = modifyInstanceDefs $ mapSnd $ const []

-- | Add an instance whose type is still unresolved.
addUnknownInstance :: QName -> TCM ()
addUnknownInstance x = do
  reportSLn "tc.decl.instance" 10 $ "adding definition " ++ show x ++ " to the instance table (the type is not yet known)"
  modifyInstanceDefs $ mapSnd (x:)

-- | Add instance to some ``class''.
addNamedInstance
  :: QName  -- ^ Name of the instance.
  -> QName  -- ^ Name of the class.
  -> TCM ()
addNamedInstance x n = do
  reportSLn "tc.decl.instance" 10 $ ("adding definition " ++ show x ++ " to instance table for " ++ show n)
  -- Mark x as instance for n.
  modifySignature $ updateDefinition x $ \ d -> d { defInstance = Just n }
  -- Add x to n's instances.
  modifyInstanceDefs $ mapFst $ Map.insertWith (++) n [x]
