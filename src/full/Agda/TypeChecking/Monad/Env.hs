
module Agda.TypeChecking.Monad.Env where

import Control.Monad.Reader
import qualified Data.List as List
import qualified Data.Map as Map
import Data.Monoid

import Agda.Syntax.Common
import Agda.Syntax.Abstract.Name

import Agda.TypeChecking.Monad.Base

-- | Get the name of the current module, if any.
{-# SPECIALIZE currentModule :: TCM ModuleName #-}
{-# SPECIALIZE currentModule :: ReduceM ModuleName #-}
currentModule :: MonadTCEnv m => m ModuleName
currentModule = asksTC envCurrentModule

-- | Set the name of the current module.
withCurrentModule :: ModuleName -> TCM a -> TCM a
withCurrentModule m =
    localTC $ \ e -> e { envCurrentModule = m }

-- | Get the number of variables bound by anonymous modules.
{-# SPECIALIZE getAnonymousVariables :: ModuleName -> TCM Nat #-}
{-# SPECIALIZE getAnonymousVariables :: ModuleName -> ReduceM Nat #-}
getAnonymousVariables :: MonadTCEnv m => ModuleName -> m Nat
getAnonymousVariables m = do
  ms <- asksTC envAnonymousModules
  return $ sum [ n | (m', n) <- ms, mnameToList m' `List.isPrefixOf` mnameToList m ]

-- | Add variables bound by an anonymous module.
withAnonymousModule :: ModuleName -> Nat -> TCM a -> TCM a
withAnonymousModule m n =
  localTC $ \ e -> e { envAnonymousModules = (m, n) : envAnonymousModules e }

-- | Set the current environment to the given
withEnv :: TCEnv -> TCM a -> TCM a
withEnv env = localTC $ \ env0 -> env
  -- Keep persistent settings
  { envPrintMetasBare         = envPrintMetasBare env0
  }

-- | Get the current environment
getEnv :: TCM TCEnv
getEnv = askTC

-- | Increases the module nesting level by one in the given
-- computation.
withIncreasedModuleNestingLevel :: TCM a -> TCM a
withIncreasedModuleNestingLevel =
  localTC $ \ e -> e { envModuleNestingLevel =
                       envModuleNestingLevel e + 1 }

-- | Set highlighting level
withHighlightingLevel :: HighlightingLevel -> TCM a -> TCM a
withHighlightingLevel h = localTC $ \ e -> e { envHighlightingLevel = h }

withoutOptionsChecking :: TCM a -> TCM a
withoutOptionsChecking = localTC $ \ e -> e { envCheckOptionConsistency = False }

-- | Restore setting for 'ExpandLast' to default.
doExpandLast :: TCM a -> TCM a
doExpandLast = localTC $ \ e -> e { envExpandLast = ExpandLast }

dontExpandLast :: TCM a -> TCM a
dontExpandLast = localTC $ \ e -> e { envExpandLast = DontExpandLast }

-- | If the reduced did a proper match (constructor or literal pattern),
--   then record this as simplification step.
{-# SPECIALIZE performedSimplification :: TCM a -> TCM a #-}
performedSimplification :: MonadTCEnv m => m a -> m a
performedSimplification = localTC $ \ e -> e { envSimplification = YesSimplification }

{-# SPECIALIZE performedSimplification' :: Simplification -> TCM a -> TCM a #-}
performedSimplification' :: MonadTCEnv m => Simplification -> m a -> m a
performedSimplification' simpl = localTC $ \ e -> e { envSimplification = simpl `mappend` envSimplification e }

getSimplification :: MonadTCEnv m => m Simplification
getSimplification = asksTC envSimplification

-- * Controlling reduction.

-- | Lens for 'AllowedReductions'.
updateAllowedReductions :: (AllowedReductions -> AllowedReductions) -> TCEnv -> TCEnv
updateAllowedReductions f e = e { envAllowedReductions = f (envAllowedReductions e) }

modifyAllowedReductions :: (AllowedReductions -> AllowedReductions) -> TCM a -> TCM a
modifyAllowedReductions = localTC . updateAllowedReductions

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
insideDotPattern = localTC $ \ e -> e { envInsideDotPattern = True }

isInsideDotPattern :: TCM Bool
isInsideDotPattern = asksTC envInsideDotPattern

-- | Don't use call-by-need evaluation for the given computation.
callByName :: TCM a -> TCM a
callByName = localTC $ \ e -> e { envCallByNeed = False }
