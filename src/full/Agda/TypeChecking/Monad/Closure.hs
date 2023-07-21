{-# OPTIONS_GHC -Wunused-imports #-}

module Agda.TypeChecking.Monad.Closure where

import Control.Monad

import Agda.TypeChecking.Monad.Base
import Agda.TypeChecking.Monad.Env
import Agda.TypeChecking.Monad.State

import Agda.Utils.Lens

enterClosure :: (MonadTCEnv m, ReadTCState m, LensClosure c a)
             => c -> (a -> m b) -> m b
enterClosure c k | Closure _sig env scope cps x <- c ^. lensClosure = do
  isDbg <- viewTC eIsDebugPrinting
  withScope_ scope
    $ locallyTCState stModuleCheckpoints (const cps)
    $ withEnv env{ envIsDebugPrinting = isDbg }
    $ k x

withClosure :: (MonadTCEnv m, ReadTCState m) => Closure a -> (a -> m b) -> m (Closure b)
withClosure cl k = enterClosure cl $ k >=> buildClosure

mapClosure :: (MonadTCEnv m, ReadTCState m) => (a -> m b) -> Closure a -> m (Closure b)
mapClosure = flip withClosure
