
module TypeChecking.Monad.Env where

import Control.Monad.Reader

import Syntax.Abstract.Name

import TypeChecking.Monad.Base

-- | Get the name of the current module, if any.
currentModule :: MonadTCM tcm => tcm ModuleName
currentModule = asks envCurrentModule

-- | Set the name of the current module.
withCurrentModule :: MonadTCM tcm => ModuleName -> tcm a -> tcm a
withCurrentModule m =
    local $ \e -> e { envCurrentModule = m }

-- | Set the current environment to the given 
withEnv :: MonadTCM tcm => TCEnv -> tcm a -> tcm a
withEnv env m = local (const env) m

-- | Get the current environmnet
getEnv :: MonadTCM tcm => tcm TCEnv
getEnv = ask

