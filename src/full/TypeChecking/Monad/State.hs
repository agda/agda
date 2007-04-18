
module TypeChecking.Monad.State where

import Control.Applicative
import Control.Monad.State

import Syntax.Scope.Base
import qualified Syntax.Concrete.Name as C
import Syntax.Abstract.Name

import TypeChecking.Monad.Base
import TypeChecking.Monad.Options

import Utils.Hash

-- | Reset the type checking state.
resetState :: MonadTCM tcm => tcm ()
resetState = liftTCM $ do
    opts <- commandLineOptions
    put initState
    setCommandLineOptions opts

-- | Set the current scope.
setScope :: MonadTCM tcm => ScopeInfo -> tcm ()
setScope scope = liftTCM $ modify $ \s -> s { stScope = scope }

-- | Get the current scope.
getScope :: MonadTCM tcm => tcm ScopeInfo
getScope = liftTCM $ gets stScope

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

-- | Set the top-level module. This affects the global module id of freshly
--   generated names.
setTopLevelModule :: MonadTCM tcm => C.QName -> tcm ()
setTopLevelModule x =
  modify $ \s -> s
    { stFreshThings = (stFreshThings s)
      { fName = setModule (hash (show x)) $ fName $ stFreshThings s
      }
    }
  where
    setModule m (NameId n _) = NameId n m

