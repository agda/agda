
module TypeChecking.Monad.State where

import Control.Monad.State

import Syntax.Scope

import TypeChecking.Monad.Base
import TypeChecking.Monad.Options

-- | Reset the type checking state.
resetState :: MonadTCM tcm => tcm ()
resetState = liftTCM $ do
    opts <- commandLineOptions
    put initState
    setCommandLineOptions opts

-- | Set the current scope.
setScope :: MonadTCM tcm => ScopeInfo -> tcm ()
setScope scope = liftTCM $ modify $ \s -> s { stScopeInfo = scope }

-- | Get the current scope.
getScope :: MonadTCM tcm => tcm ScopeInfo
getScope = liftTCM $ gets stScopeInfo


withScope :: MonadTCM tcm => ScopeInfo -> tcm a -> tcm a
withScope scope m =
    do	scope0 <- getScope
	setScope scope
	r <- m
	setScope scope0
        return r

