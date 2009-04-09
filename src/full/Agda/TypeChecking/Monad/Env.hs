
module Agda.TypeChecking.Monad.Env where

import Control.Monad.Reader
import Data.List

import Agda.Syntax.Common
import Agda.Syntax.Abstract.Name

import Agda.TypeChecking.Monad.Base

-- | Get the name of the current module, if any.
currentModule :: MonadTCM tcm => tcm ModuleName
currentModule = asks envCurrentModule

-- | Set the name of the current module.
withCurrentModule :: MonadTCM tcm => ModuleName -> tcm a -> tcm a
withCurrentModule m =
    local $ \e -> e { envCurrentModule = m }

-- | Get the number of variables bound by anonymous modules.
getAnonymousVariables :: MonadTCM tcm => ModuleName -> tcm Nat
getAnonymousVariables m = do
  ms <- asks envAnonymousModules
  return $ sum [ n | (m', n) <- ms, mnameToList m' `isPrefixOf` mnameToList m ]

-- | Add variables bound by an anonymous module.
withAnonymousModule :: MonadTCM tcm => ModuleName -> Nat -> tcm a -> tcm a
withAnonymousModule m n =
  local $ \e -> e { envAnonymousModules   = (m, n) : envAnonymousModules e
                  }

-- | Set the current environment to the given
withEnv :: MonadTCM tcm => TCEnv -> tcm a -> tcm a
withEnv env m = local (const env) m

-- | Get the current environmnet
getEnv :: MonadTCM tcm => tcm TCEnv
getEnv = ask

