
module TypeChecking.Monad.State where

import Control.Monad.State

import Syntax.Scope

import TypeChecking.Monad.Base
import TypeChecking.Monad.Options

-- | Reset the type checking state.
resetState :: TCM ()
resetState =
    do	opts <- commandLineOptions
	put initState
	setCommandLineOptions opts

-- | Set the current scope.
setScope :: ScopeInfo -> TCM ()
setScope scope = modify $ \s -> s { stScopeInfo = scope }

-- | Get the current scope.
getScope :: TCM ScopeInfo
getScope = gets stScopeInfo


withScope :: ScopeInfo -> TCM a -> TCM a
withScope scope m =
    do	scope0 <- getScope
	setScope scope
	r <- m
	setScope scope0
        return r

