{-# OPTIONS_GHC -Wunused-imports #-}

module Agda.TypeChecking.Monad.Env where

import qualified Data.List as List

import Data.Maybe (fromMaybe)

import Agda.Syntax.Common
import Agda.Syntax.Abstract.Name

import Agda.TypeChecking.Monad.Base

import qualified Agda.Utils.SmallSet as SmallSet

import Agda.Utils.Impossible

-- | Get the name of the current module, if any.
{-# SPECIALIZE currentModule :: TCM ModuleName #-}
{-# SPECIALIZE currentModule :: ReduceM ModuleName #-}
currentModule :: MonadTCEnv m => m ModuleName
currentModule = viewTC eCurrentModule

{-# INLINE withCurrentModule #-}
-- | Set the name of the current module.
withCurrentModule :: (MonadTCEnv m) => ModuleName -> m a -> m a
withCurrentModule m = localTC $ set eCurrentModule m

-- | Get the path of the currently checked file
getCurrentPath :: (MonadTCEnv m, MonadFileId m) => m AbsolutePath
getCurrentPath = do
  i <- fromMaybe __IMPOSSIBLE__ <$> viewTC eCurrentPath
  fileFromId i

-- | Get the number of variables bound by anonymous modules.
{-# SPECIALIZE getAnonymousVariables :: ModuleName -> TCM Nat #-}
{-# SPECIALIZE getAnonymousVariables :: ModuleName -> ReduceM Nat #-}
getAnonymousVariables :: MonadTCEnv m => ModuleName -> m Nat
getAnonymousVariables m = do
  ms <- viewTC eAnonymousModules
  return $ sum [ n | (m', n) <- ms, mnameToList m' `List.isPrefixOf` mnameToList m ]

{-# INLINE withAnonymousModule #-}
-- | Add variables bound by an anonymous module.
withAnonymousModule :: ModuleName -> Nat -> TCM a -> TCM a
withAnonymousModule m n =
  localTC $ over eAnonymousModules \ms -> (m, n) : ms

{-# INLINE withEnv #-}
-- | Set the current environment to the given
withEnv :: MonadTCEnv m => TCEnv -> m a -> m a
withEnv env = localTC \env0 ->
  -- Keep persistent settings
  env & ePrintMetasBare .~ (env0 ^. ePrintMetasBare)

-- | Get the current environment
getEnv :: TCM TCEnv
getEnv = askTC

{-# INLINE withHighlightingLevel #-}
-- | Set highlighting level
withHighlightingLevel :: HighlightingLevel -> TCM a -> TCM a
withHighlightingLevel h = localTC $ set eHighlightingLevel h

{-# INLINE doExpandLast #-}
-- | Restore setting for 'ExpandLast' to default.
doExpandLast :: TCM a -> TCM a
doExpandLast = localTC $ over eExpandLast setExpand where
    setExpand ReallyDontExpandLast = ReallyDontExpandLast
    setExpand _                    = ExpandLast

{-# INLINE dontExpandLast #-}
dontExpandLast :: TCM a -> TCM a
dontExpandLast = localTC $ set eExpandLast DontExpandLast

{-# INLINE reallyDontExpandLast #-}
reallyDontExpandLast :: TCM a -> TCM a
reallyDontExpandLast = localTC $ set eExpandLast ReallyDontExpandLast

-- | If the reduced did a proper match (constructor or literal pattern),
--   then record this as simplification step.
{-# INLINE performedSimplification #-}
performedSimplification :: MonadTCEnv m => m a -> m a
performedSimplification = localTC $ set eSimplification YesSimplification

{-# INLINE performedSimplification' #-}
performedSimplification' :: MonadTCEnv m => Simplification -> m a -> m a
performedSimplification' simpl = localTC $ over' eSimplification (simpl <>)

getSimplification :: MonadTCEnv m => m Simplification
getSimplification = viewTC eSimplification

-- * Controlling reduction.

-- | Lens for 'AllowedReductions'.
updateAllowedReductions :: (AllowedReductions -> AllowedReductions) -> TCEnv -> TCEnv
updateAllowedReductions = over eAllowedReductions

{-# INLINE modifyAllowedReductions #-}
modifyAllowedReductions :: MonadTCEnv m => (AllowedReductions -> AllowedReductions) -> m a -> m a
modifyAllowedReductions = localTC . updateAllowedReductions

{-# INLINE putAllowedReductions #-}
putAllowedReductions :: MonadTCEnv m => AllowedReductions -> m a -> m a
putAllowedReductions = modifyAllowedReductions . const

{-# INLINE onlyReduceProjections #-}
-- | Reduce @Def f vs@ only if @f@ is a projection.
onlyReduceProjections :: MonadTCEnv m => m a -> m a
onlyReduceProjections = modifyAllowedReductions $ SmallSet.intersection $
  SmallSet.singleton ProjectionReductions

{-# INLINE allowAllReductions #-}
-- | Allow all reductions except for non-terminating functions (default).
allowAllReductions :: MonadTCEnv m => m a -> m a
allowAllReductions = putAllowedReductions allReductions

{-# INLINE allowNonTerminatingReductions #-}
-- | Allow all reductions including non-terminating functions.
allowNonTerminatingReductions :: MonadTCEnv m => m a -> m a
allowNonTerminatingReductions = putAllowedReductions reallyAllReductions

{-# INLINE onlyReduceTypes #-}
-- | Allow all reductions when reducing types. Otherwise only allow
--   inlined functions to be unfolded.
onlyReduceTypes :: MonadTCEnv m => m a -> m a
onlyReduceTypes = modifyAllowedReductions $ SmallSet.intersection $
  SmallSet.fromList [TypeLevelReductions, InlineReductions]

{-# INLINE typeLevelReductions #-}
-- | Update allowed reductions when working on types
typeLevelReductions :: MonadTCEnv m => m a -> m a
typeLevelReductions = modifyAllowedReductions $ \reds -> if
  | TypeLevelReductions `SmallSet.member` reds ->
      if NonTerminatingReductions `SmallSet.member` reds
       then reallyAllReductions
       else allReductions
  | otherwise -> reds

-- * Concerning 'envInsideDotPattern'

{-# INLINE insideDotPattern #-}
insideDotPattern :: TCM a -> TCM a
insideDotPattern = localTC $ set eInsideDotPattern True

isInsideDotPattern :: TCM Bool
isInsideDotPattern = viewTC eInsideDotPattern

{-# INLINE callByName #-}
-- | Don't use call-by-need evaluation for the given computation.
callByName :: TCM a -> TCM a
callByName = localTC $ set eCallByNeed False

{-# INLINE dontFoldLetBindings #-}
-- | Don't fold let bindings when printing. This is a bit crude since it disables any folding of let
--   bindings at all. In many cases it's better to use `removeLetBinding` before printing to drop
--   the let bindings that should not be folded.
dontFoldLetBindings :: MonadTCEnv m => m a -> m a
dontFoldLetBindings = localTC $ set eFoldLetBindings False
