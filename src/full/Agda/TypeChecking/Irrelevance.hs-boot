{-# OPTIONS_GHC -Wunused-imports #-}

module Agda.TypeChecking.Irrelevance where

import Agda.Syntax.Internal (LensSort)

import Agda.TypeChecking.Monad.Base (MonadBlock)
import {-# SOURCE #-} Agda.TypeChecking.Pretty (PrettyTCM)
import Agda.TypeChecking.Monad.Pure (PureTCM)

isPropM
  :: (LensSort a, PrettyTCM a, PureTCM m, MonadBlock m)
  => a -> m Bool
