module Agda.TypeChecking.Monad.Env where


import qualified Data.List as List

import Data.Maybe (fromMaybe)


import Agda.Syntax.Common
import Agda.Syntax.Abstract.Name

import Agda.TypeChecking.Monad.Base

import Agda.Utils.FileName
import Agda.Utils.Function

import Agda.Utils.Impossible

-- | Get the name of the current module, if any.
{-# SPECIALIZE currentModule :: TCM ModuleName #-}
{-# SPECIALIZE currentModule :: ReduceM ModuleName #-}
currentModule :: MonadTCEnv m => m ModuleName
currentModule = asksTC envCurrentModule

-- | Set the name of the current module.
withCurrentModule :: ModuleName -> TCM a -> TCM a
withCurrentModule m =
    localTC $ \ e -> e { envCurrentModule = m }

-- | Get the path of the currently checked file
getCurrentPath :: MonadTCEnv m => m AbsolutePath
getCurrentPath = fromMaybe __IMPOSSIBLE__ <$> asksTC envCurrentPath

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
withEnv :: MonadTCEnv m => TCEnv -> m a -> m a
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
doExpandLast = localTC $ \ e -> e { envExpandLast = setExpand (envExpandLast e) }
  where
    setExpand ReallyDontExpandLast = ReallyDontExpandLast
    setExpand _                    = ExpandLast

dontExpandLast :: TCM a -> TCM a
dontExpandLast = localTC $ \ e -> e { envExpandLast = DontExpandLast }

reallyDontExpandLast :: TCM a -> TCM a
reallyDontExpandLast = localTC $ \ e -> e { envExpandLast = ReallyDontExpandLast }

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

modifyAllowedReductions :: MonadTCEnv m => (AllowedReductions -> AllowedReductions) -> m a -> m a
modifyAllowedReductions = localTC . updateAllowedReductions

putAllowedReductions :: MonadTCEnv m => AllowedReductions -> m a -> m a
putAllowedReductions = modifyAllowedReductions . const

-- | Reduce @Def f vs@ only if @f@ is a projection.
onlyReduceProjections :: MonadTCEnv m => m a -> m a
onlyReduceProjections = putAllowedReductions [ProjectionReductions]

-- | Allow all reductions except for non-terminating functions (default).
allowAllReductions :: MonadTCEnv m => m a -> m a
allowAllReductions = putAllowedReductions allReductions

-- | Allow all reductions including non-terminating functions.
allowNonTerminatingReductions :: MonadTCEnv m => m a -> m a
allowNonTerminatingReductions = putAllowedReductions $ [NonTerminatingReductions] ++ allReductions

-- | Allow all reductions when reducing types
onlyReduceTypes :: MonadTCEnv m => m a -> m a
onlyReduceTypes = putAllowedReductions [TypeLevelReductions]

-- | Update allowed reductions when working on types
typeLevelReductions :: MonadTCEnv m => m a -> m a
typeLevelReductions = modifyAllowedReductions $ \reds -> if
  | TypeLevelReductions `elem` reds ->
      applyWhen (NonTerminatingReductions `elem` reds) (NonTerminatingReductions:) allReductions
  | otherwise -> reds

-- * Concerning 'envInsideDotPattern'

insideDotPattern :: TCM a -> TCM a
insideDotPattern = localTC $ \ e -> e { envInsideDotPattern = True }

isInsideDotPattern :: TCM Bool
isInsideDotPattern = asksTC envInsideDotPattern

-- | Don't use call-by-need evaluation for the given computation.
callByName :: TCM a -> TCM a
callByName = localTC $ \ e -> e { envCallByNeed = False }
