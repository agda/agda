
module Agda.TypeChecking.Monad.Env where

import Control.Monad.Reader
import qualified Data.List as List
import Data.Monoid

import Agda.Syntax.Common
import Agda.Syntax.Abstract.Name

import Agda.TypeChecking.Monad.Base

-- | Get the name of the current module, if any.
{-# SPECIALIZE currentModule :: TCM ModuleName #-}
{-# SPECIALIZE currentModule :: ReduceM ModuleName #-}
currentModule :: MonadReader TCEnv m => m ModuleName
currentModule = asks envCurrentModule

-- | Set the name of the current module.
withCurrentModule :: ModuleName -> TCM a -> TCM a
withCurrentModule m =
    local $ \e -> e { envCurrentModule = m }

-- | Get the number of variables bound by anonymous modules.
{-# SPECIALIZE getAnonymousVariables :: ModuleName -> TCM Nat #-}
{-# SPECIALIZE getAnonymousVariables :: ModuleName -> ReduceM Nat #-}
getAnonymousVariables :: MonadReader TCEnv m => ModuleName -> m Nat
getAnonymousVariables m = do
  ms <- asks envAnonymousModules
  return $ sum [ n | (m', n) <- ms, mnameToList m' `List.isPrefixOf` mnameToList m ]

-- | Add variables bound by an anonymous module.
withAnonymousModule :: ModuleName -> Nat -> TCM a -> TCM a
withAnonymousModule m n =
  local $ \e -> e { envAnonymousModules   = (m, n) : envAnonymousModules e
                  }

-- | Set the current environment to the given
withEnv :: TCEnv -> TCM a -> TCM a
withEnv env = local $ \ env0 -> env
  -- Keep persistent settings
  { envAllowDestructiveUpdate = envAllowDestructiveUpdate env0
  , envPrintMetasBare         = envPrintMetasBare env0
  }

-- | Get the current environment
getEnv :: TCM TCEnv
getEnv = ask

-- | Increases the module nesting level by one in the given
-- computation.
withIncreasedModuleNestingLevel :: TCM a -> TCM a
withIncreasedModuleNestingLevel =
  local (\e -> e { envModuleNestingLevel =
                     envModuleNestingLevel e + 1 })

-- | Set highlighting level
withHighlightingLevel :: HighlightingLevel -> TCM a -> TCM a
withHighlightingLevel h = local $ \e -> e { envHighlightingLevel = h }

-- | Restore setting for 'ExpandLast' to default.
doExpandLast :: TCM a -> TCM a
doExpandLast = local $ \ e -> e { envExpandLast = ExpandLast }

dontExpandLast :: TCM a -> TCM a
dontExpandLast = local $ \ e -> e { envExpandLast = DontExpandLast }

-- | If the reduced did a proper match (constructor or literal pattern),
--   then record this as simplification step.
{-# SPECIALIZE performedSimplification :: TCM a -> TCM a #-}
performedSimplification :: MonadReader TCEnv m => m a -> m a
performedSimplification = local $ \ e -> e { envSimplification = YesSimplification }

{-# SPECIALIZE performedSimplification' :: Simplification -> TCM a -> TCM a #-}
performedSimplification' :: MonadReader TCEnv m => Simplification -> m a -> m a
performedSimplification' simpl = local $ \ e -> e { envSimplification = simpl `mappend` envSimplification e }

getSimplification :: MonadReader TCEnv m => m Simplification
getSimplification = asks envSimplification

-- * Controlling reduction.

-- | Lens for 'AllowedReductions'.
updateAllowedReductions :: (AllowedReductions -> AllowedReductions) -> TCEnv -> TCEnv
updateAllowedReductions f e = e { envAllowedReductions = f (envAllowedReductions e) }

modifyAllowedReductions :: (AllowedReductions -> AllowedReductions) -> TCM a -> TCM a
modifyAllowedReductions = local . updateAllowedReductions

putAllowedReductions :: AllowedReductions -> TCM a -> TCM a
putAllowedReductions = modifyAllowedReductions . const

-- | Reduce @Def f vs@ only if @f@ is a projection.
onlyReduceProjections :: TCM a -> TCM a
onlyReduceProjections = putAllowedReductions [ProjectionReductions]

-- | Allow all reductions except for non-terminating functions (default).
allowAllReductions :: TCM a -> TCM a
allowAllReductions = putAllowedReductions allReductions

-- | Allow all reductions including non-terminating functions.
allowNonTerminatingReductions :: TCM a -> TCM a
allowNonTerminatingReductions = putAllowedReductions $ [NonTerminatingReductions] ++ allReductions

-- * Concerning 'envInsideDotPattern'

insideDotPattern :: TCM a -> TCM a
insideDotPattern = local $ \e -> e { envInsideDotPattern = True }

isInsideDotPattern :: TCM Bool
isInsideDotPattern = asks envInsideDotPattern
