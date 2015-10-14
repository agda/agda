{-# LANGUAGE FlexibleContexts #-}

module Agda.TypeChecking.Monad.Context where

import Control.Monad.Reader

import Agda.Syntax.Common (Dom)
import Agda.Syntax.Internal
import Agda.TypeChecking.Monad.Base

getContext   :: MonadReader TCEnv m => m [Dom (Name, Type)]
getContextId :: MonadReader TCEnv m => m [CtxId]
