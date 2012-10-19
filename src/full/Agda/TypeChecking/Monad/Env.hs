
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
withEnv env m = local (\env0 -> env { envAllowDestructiveUpdate = envAllowDestructiveUpdate env0 }) m

-- | Get the current environment
getEnv :: TCM TCEnv
getEnv = ask

-- | Increases the module nesting level by one in the given
-- computation.
withIncreasedModuleNestingLevel :: TCM a -> TCM a
withIncreasedModuleNestingLevel =
  local (\e -> e { envModuleNestingLevel =
                     envModuleNestingLevel e + 1 })
