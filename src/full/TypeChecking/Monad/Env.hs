
module TypeChecking.Monad.Env where

import Control.Monad.Reader

import Syntax.Abstract.Name

import TypeChecking.Monad.Base

-- | Get the name of the current module, if any.
currentModule :: TCM ModuleName
currentModule = asks envCurrentModule

-- | Set the name of the current module.
withCurrentModule :: ModuleName -> TCM a -> TCM a
withCurrentModule m =
    local $ \e -> e { envCurrentModule = m }

-- | Set the current environment to the given 
withEnv :: TCEnv -> TCM a -> TCM a
withEnv env m = local (const env) m

-- | Get the current environmnet
getEnv :: TCM TCEnv
getEnv = ask


