{-# LANGUAGE FlexibleContexts #-}

module Agda.TypeChecking.Monad.Context where

import Control.Monad.Reader

import Agda.Syntax.Internal
import Agda.TypeChecking.Monad.Base

checkpointSubstitution :: MonadTCEnv tcm => CheckpointId -> tcm Substitution
