{-# LANGUAGE CPP #-}

-- | Lenses for 'TCState' and more.

module Agda.TypeChecking.Monad.State where

import Control.Applicative
import qualified Control.Exception as E
import Control.Monad.State
import Data.Set (Set)
import Data.Map as Map
import qualified Data.Set as Set

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
import Agda.TypeChecking.Monad.Base.Benchmark
import {-# SOURCE #-} Agda.TypeChecking.Monad.Options

import Agda.Utils.Hash
import qualified Agda.Utils.HashMap as HMap
import Agda.Utils.Monad (bracket_)
import Agda.Utils.Pretty
import Agda.Utils.Tuple

#include "../../undefined.h"
import Agda.Utils.Impossible

-- | Resets the non-persistent part of the type checking state.

resetState :: TCM ()
resetState = do
    pers <- gets stPersistent
    put $ initState { stPersistent = pers }

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
localTCState = bracket_ get $ \ s -> do
   b <- getBenchmark
   put s
   modifyBenchmark $ const b

---------------------------------------------------------------------------
-- * Lens for persistent state
---------------------------------------------------------------------------

updatePersistentState :: (PersistentTCState -> PersistentTCState) -> (TCState -> TCState)
updatePersistentState f s = s { stPersistent = f (stPersistent s) }

modifyPersistentState :: (PersistentTCState -> PersistentTCState) -> TCM ()
modifyPersistentState = modify . updatePersistentState

---------------------------------------------------------------------------
-- * Scope
---------------------------------------------------------------------------

-- | Get the current scope.
getScope :: TCM ScopeInfo
getScope = gets stScope

-- | Set the current scope.
setScope :: ScopeInfo -> TCM ()
setScope scope = modifyScope (const scope)

-- | Modify the current scope.
modifyScope :: (ScopeInfo -> ScopeInfo) -> TCM ()
modifyScope f = modify $ \ s -> s { stScope = f (stScope s) }

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
modifySignature f = modify $ \s -> s { stSignature = f $ stSignature s }

modifyImportedSignature :: (Signature -> Signature) -> TCM ()
modifyImportedSignature f = modify $ \s -> s { stImports = f $ stImports s }

getSignature :: TCM Signature
getSignature = gets stSignature

getImportedSignature :: TCM Signature
getImportedSignature = gets stImports

setSignature :: Signature -> TCM ()
setSignature sig = modifySignature $ const sig

setImportedSignature :: Signature -> TCM ()
setImportedSignature sig = modify $ \s -> s { stImports = sig }

-- | Run some computation in a different signature, restore original signature.
withSignature :: Signature -> TCM a -> TCM a
withSignature sig m = do
  sig0 <- getSignature
  setSignature sig
  r <- m
  setSignature sig0
  return r

-- ** Modifiers for parts of the signature

lookupDefinition :: QName -> Signature -> Maybe Definition
lookupDefinition q sig = HMap.lookup q $ sigDefinitions sig

updateDefinition :: QName -> (Definition -> Definition) -> Signature -> Signature
updateDefinition q f sig = sig { sigDefinitions = HMap.adjust f q (sigDefinitions sig) }

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
setTopLevelModule x =
  modify $ \s -> s
    { stFreshThings = (stFreshThings s)
      { fName = NameId 0 $ hashString (show x)
      }
    }

-- | Use a different top-level module for a computation. Used when generating
--   names for imported modules.
withTopLevelModule :: C.QName -> TCM a -> TCM a
withTopLevelModule x m = do
  next <- gets $ fName . stFreshThings
  setTopLevelModule x
  y <- m
  modify $ \s -> s { stFreshThings = (stFreshThings s) { fName = next } }
  return y

---------------------------------------------------------------------------
-- * Haskell imports
---------------------------------------------------------------------------

-- | Tell the compiler to import the given Haskell module.
addHaskellImport :: String -> TCM ()
addHaskellImport i =
  modify $ \s -> s { stHaskellImports = Set.insert i $ stHaskellImports s }

-- | Get the Haskell imports.
getHaskellImports :: TCM (Set String)
getHaskellImports = gets stHaskellImports

---------------------------------------------------------------------------
-- * Interaction output callback
---------------------------------------------------------------------------

getInteractionOutputCallback :: TCM InteractionOutputCallback
getInteractionOutputCallback
  = gets $ stInteractionOutputCallback . stPersistent

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
getPatternSyns = gets stPatternSyns

setPatternSyns :: PatternSynDefns -> TCM ()
setPatternSyns m = modifyPatternSyns (const m)

-- | Lens for 'stPatternSyns'.
modifyPatternSyns :: (PatternSynDefns -> PatternSynDefns) -> TCM ()
modifyPatternSyns f = modify $ \s -> s { stPatternSyns = f (stPatternSyns s) }

getPatternSynImports :: TCM PatternSynDefns
getPatternSynImports = gets stPatternSynImports

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
theBenchmark = stBenchmark . stPersistent

-- | Lens map for 'Benchmark'.
updateBenchmark :: (Benchmark -> Benchmark) -> TCState -> TCState
updateBenchmark f = updatePersistentState $ \ s -> s { stBenchmark = f (stBenchmark s) }

-- | Lens getter for 'Benchmark' from 'TCM'.
getBenchmark :: TCM Benchmark
getBenchmark = gets $ theBenchmark

-- | Lens modify for 'Benchmark'.
modifyBenchmark :: (Benchmark -> Benchmark) -> TCM ()
modifyBenchmark = modify . updateBenchmark

-- | Run a fresh instance of the TCM (with initial state).
--   'Benchmark' info is preserved.
freshTCM :: TCM a -> TCM (Either TCErr a)
freshTCM m = do
  -- Prepare an initial state with current benchmark info.
  b <- getBenchmark
  let s = updateBenchmark (const b) initState
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
      return $ Right a

---------------------------------------------------------------------------
-- * Instance definitions
---------------------------------------------------------------------------

-- | Lens for 'stInstanceDefs'.
updateInstanceDefs :: (TempInstanceTable -> TempInstanceTable) -> (TCState -> TCState)
updateInstanceDefs f s = s { stInstanceDefs = f $ stInstanceDefs s }

modifyInstanceDefs :: (TempInstanceTable -> TempInstanceTable) -> TCM ()
modifyInstanceDefs = modify . updateInstanceDefs

getAllInstanceDefs :: TCM TempInstanceTable
getAllInstanceDefs = gets stInstanceDefs

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
