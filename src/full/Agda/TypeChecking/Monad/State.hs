
module Agda.TypeChecking.Monad.State where

import Control.Applicative
import Control.Monad.State
import Data.Set (Set)
import Data.Map
import qualified Data.Set as Set

import Agda.Syntax.Common
import Agda.Syntax.Scope.Base
import qualified Agda.Syntax.Concrete.Name as C
import Agda.Syntax.Abstract.Name

import Agda.TypeChecking.Monad.Base

import Agda.Utils.Hash

-- | Resets the type checking state. The persistent command line
-- options are preserved.

resetState :: MonadTCM tcm => tcm ()
resetState = liftTCM $ do
    opts <- stPersistentOptions <$> get
    put $ initState { stPersistentOptions = opts }

-- | Set the current scope.
setScope :: MonadTCM tcm => ScopeInfo -> tcm ()
setScope scope = liftTCM $ modify $ \s -> s { stScope = scope }

-- | Get the current scope.
getScope :: MonadTCM tcm => tcm ScopeInfo
getScope = liftTCM $ gets stScope

-- | Sets stExtLambdaTele .
setExtLambdaTele :: MonadTCM tcm => Map QName (Int , Int) -> tcm ()
setExtLambdaTele tele = liftTCM $ modify $ \s -> s { stExtLambdaTele = tele }

-- | Get stExtLambdaTele.
getExtLambdaTele :: MonadTCM tcm => tcm (Map QName (Int , Int))
getExtLambdaTele = liftTCM $ gets stExtLambdaTele

addExtLambdaTele :: MonadTCM tcm => QName -> (Int , Int) -> tcm ()
addExtLambdaTele id x = getExtLambdaTele >>= setExtLambdaTele . (insert id x)

-- | Modify the current scope.
modifyScope :: MonadTCM tcm => (ScopeInfo -> ScopeInfo) -> tcm ()
modifyScope f = do
  s <- getScope
  setScope $ f s

-- | Run a computation in a local scope.
withScope :: MonadTCM tcm => ScopeInfo -> tcm a -> tcm (a, ScopeInfo)
withScope s m = do
  s' <- getScope
  setScope s
  x   <- m
  s'' <- getScope
  setScope s'
  return (x, s'')

-- | Same as 'withScope', but discard the scope from the computation.
withScope_ :: MonadTCM tcm => ScopeInfo -> tcm a -> tcm a
withScope_ s m = fst <$> withScope s m

-- | Discard any changes to the scope by a computation.
localScope :: MonadTCM tcm => tcm a -> tcm a
localScope m = do
  scope <- getScope
  x <- m
  setScope scope
  return x

-- | Set the top-level module. This affects the global module id of freshly
--   generated names.
setTopLevelModule :: MonadTCM tcm => C.QName -> tcm ()
setTopLevelModule x =
  modify $ \s -> s
    { stFreshThings = (stFreshThings s)
      { fName = NameId 0 $ hash (show x)
      }
    }

-- | Use a different top-level module for a computation. Used when generating
--   names for imported modules.
withTopLevelModule :: MonadTCM tcm => C.QName -> tcm a -> tcm a
withTopLevelModule x m = do
  next <- gets $ fName . stFreshThings
  setTopLevelModule x
  y <- m
  modify $ \s -> s { stFreshThings = (stFreshThings s) { fName = next } }
  return y

-- | Tell the compiler to import the given Haskell module.
addHaskellImport :: MonadTCM tcm => String -> tcm ()
addHaskellImport i =
  modify $ \s -> s { stHaskellImports = Set.insert i $ stHaskellImports s }

-- | Get the Haskell imports.
getHaskellImports :: MonadTCM tcm => tcm (Set String)
getHaskellImports = gets stHaskellImports
