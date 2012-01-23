
module Agda.TypeChecking.Monad.Env where

import Control.Monad.Reader
import Data.List

import Agda.Syntax.Common
import Agda.Syntax.Abstract.Name

import Agda.TypeChecking.Monad.Base

-- | Get the name of the current module, if any.
currentModule :: TCM ModuleName
currentModule = asks envCurrentModule

-- | Set the name of the current module.
withCurrentModule :: ModuleName -> TCM a -> TCM a
withCurrentModule m =
    local $ \e -> e { envCurrentModule = m }

-- | Get the number of variables bound by anonymous modules.
getAnonymousVariables :: ModuleName -> TCM Nat
getAnonymousVariables m = do
  ms <- asks envAnonymousModules
  return $ sum [ n | (m', n) <- ms, mnameToList m' `isPrefixOf` mnameToList m ]

-- | Add variables bound by an anonymous module.
withAnonymousModule :: ModuleName -> Nat -> TCM a -> TCM a
withAnonymousModule m n =
  local $ \e -> e { envAnonymousModules   = (m, n) : envAnonymousModules e
                  }

-- | Set the current environment to the given
withEnv :: TCEnv -> TCM a -> TCM a
withEnv env m = local (const env) m

-- | Get the current environmnet
getEnv :: TCM TCEnv
getEnv = ask

-- | Leave the top level to type check local things.
leaveTopLevel :: TCM a -> TCM a
leaveTopLevel = local $ \ env -> env { envTopLevel = False }

onTopLevel :: TCM Bool
onTopLevel = asks envTopLevel

-- | Increases the module nesting level by one in the given
-- computation.
withIncreasedModuleNestingLevel :: TCM a -> TCM a
withIncreasedModuleNestingLevel =
  local (\e -> e { envModuleNestingLevel =
                     envModuleNestingLevel e + 1 })
