module Agda.TypeChecking.Opacity where

import {-# SOURCE #-} Agda.TypeChecking.Monad.Signature (HasConstInfo)
import Agda.TypeChecking.Monad.Base

import Agda.Syntax.Abstract.Name

isAccessibleDef :: TCEnv -> TCState -> Definition -> Bool

hasAccessibleDef
  :: (ReadTCState m, MonadTCEnv m, HasConstInfo m) => QName -> m Bool
