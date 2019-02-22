module Agda.TypeChecking.Errors where

import Agda.Syntax.Abstract.Name

import Agda.TypeChecking.Monad.Base

-- Misplaced SPECIALISE pragma:
-- {-# SPECIALIZE prettyError :: TCErr -> TCM String #-}
prettyError :: MonadTCM tcm => TCErr -> tcm String

topLevelModuleDropper :: (MonadTCEnv m, ReadTCState m) => m (QName -> QName)
