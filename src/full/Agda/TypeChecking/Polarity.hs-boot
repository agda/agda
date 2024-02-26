{-# OPTIONS_GHC -Wunused-imports #-}

module Agda.TypeChecking.Polarity where

import Agda.Syntax.Abstract.Name                        (QName)
import Agda.TypeChecking.Monad.Base
import Agda.TypeChecking.Monad.Builtin                  (HasBuiltins)
import Agda.TypeChecking.Monad.Context                  (MonadAddContext)
import Agda.TypeChecking.Monad.Debug                    (MonadDebug)
import Agda.TypeChecking.Polarity.Base                  (Polarity)
import {-# SOURCE #-} Agda.TypeChecking.Monad.Signature (HasConstInfo)
import {-# SOURCE #-} Agda.TypeChecking.Pretty          (MonadPretty)

computePolarity
  :: ( HasOptions m, HasConstInfo m, HasBuiltins m
     , MonadTCEnv m, MonadTCState m, MonadReduce m, MonadAddContext m, MonadTCError m
     , MonadDebug m, MonadPretty m )
  => [QName] -> m ()

composePol      :: Polarity -> Polarity -> Polarity
