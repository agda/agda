-- | Facility to test throwing internal errors.

module Agda.ImpossibleTest where

import Agda.TypeChecking.Monad.Base   ( TCM, ReduceM, runReduceM )
import Agda.TypeChecking.Monad.Debug  ( MonadDebug, __IMPOSSIBLE_VERBOSE__ )
import Agda.TypeChecking.Reduce.Monad ()

import Agda.Utils.CallStack           ( HasCallStack )
import Agda.Utils.Impossible          ( __IMPOSSIBLE__ )

-- | If the given list of words is non-empty, print them as debug message
--   (using '__IMPOSSIBLE_VERBOSE__') before raising the internal error.
impossibleTest :: (MonadDebug m, HasCallStack) => [String] -> m a
impossibleTest = \case
  []   -> __IMPOSSIBLE__
  strs -> __IMPOSSIBLE_VERBOSE__ $ unwords strs

impossibleTestReduceM :: (HasCallStack) => [String] -> TCM a
impossibleTestReduceM = runReduceM . \case
  []   -> __IMPOSSIBLE__
  strs -> __IMPOSSIBLE_VERBOSE__ $ unwords strs
