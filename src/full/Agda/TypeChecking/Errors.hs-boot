{-# OPTIONS_GHC -Wunused-imports #-}

module Agda.TypeChecking.Errors where

import Agda.Syntax.Common (Relevance)
import Agda.Syntax.Abstract.Name

import Agda.TypeChecking.Monad.Base
import {-# SOURCE #-} Agda.TypeChecking.Monad.Debug (MonadDebug)
import {-# SOURCE #-} Agda.TypeChecking.Pretty (PrettyTCM)

instance PrettyTCM TypeError
instance PrettyTCM TCErr

-- Misplaced SPECIALISE pragma:
-- {-# SPECIALIZE renderError :: TCErr -> TCM String #-}
renderError :: MonadTCM tcm => TCErr -> tcm String

topLevelModuleDropper :: (MonadDebug m, MonadTCEnv m, ReadTCState m) => m (QName -> QName)

class Verbalize a where
  verbalize :: a -> String

instance Verbalize Relevance where
