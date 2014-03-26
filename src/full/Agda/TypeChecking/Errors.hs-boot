module Agda.TypeChecking.Errors where

import Agda.TypeChecking.Monad.Base

-- Misplaced SPECIALISE pragma:
-- {-# SPECIALIZE prettyError :: TCErr -> TCM String #-}
prettyError :: MonadTCM tcm => TCErr -> tcm String
