
module Agda.TypeChecking.Monad.State where

import Control.Applicative
import Control.Monad.State
import Data.Set (Set)
import Data.Map as Map
import qualified Data.Set as Set

import Agda.Syntax.Common
import Agda.Syntax.Scope.Base
import qualified Agda.Syntax.Concrete.Name as C
import Agda.Syntax.Abstract (PatternSynDefn, PatternSynDefns)
import Agda.Syntax.Abstract.Name

import Agda.TypeChecking.Monad.Base

import Agda.Utils.Hash

-- | Resets the non-persistent part of the type checking state.

resetState :: TCM ()
resetState = do
    pers <- stPersistent <$> get
    put $ initState { stPersistent = pers }

-- | Resets all of the type checking state.

resetAllState :: TCM ()
resetAllState = put initState

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

-- | Set the current scope.
setScope :: ScopeInfo -> TCM ()
setScope scope = modify $ \s -> s { stScope = scope }

-- | Get the current scope.
getScope :: TCM ScopeInfo
getScope = gets stScope

-- | Modify the current scope.
modifyScope :: (ScopeInfo -> ScopeInfo) -> TCM ()
modifyScope f = do
  s <- getScope
  setScope $ f s

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
