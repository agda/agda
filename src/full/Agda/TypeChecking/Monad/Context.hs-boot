{-# LANGUAGE FlexibleContexts #-}

module Agda.TypeChecking.Monad.Context where

import Control.Monad.Reader

import Agda.Syntax.Common
import Agda.Syntax.Internal
import Agda.Syntax.Position
import Agda.TypeChecking.Monad.Base

checkpointSubstitution :: MonadTCEnv tcm => CheckpointId -> tcm Substitution

class Monad m => MonadAddContext m where
  addCtx :: Name -> Dom Type -> m a -> m a
  withFreshName :: Range -> ArgName -> (Name -> m a) -> m a

instance MonadAddContext TCM
