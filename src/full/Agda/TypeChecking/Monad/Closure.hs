module Agda.TypeChecking.Monad.Closure where

import Control.Monad

import Agda.TypeChecking.Monad.Base
import Agda.TypeChecking.Monad.Env
import Agda.TypeChecking.Monad.State

enterClosure :: (MonadTCEnv m, ReadTCState m)
             => Closure a -> (a -> m b) -> m b
enterClosure (Closure sig env scope cps x) k = do
  isDbg <- viewTC eIsDebugPrinting
  withScope_ scope
    $ locallyTCState stModuleCheckpoints (const cps)
    $ withEnv env{ envIsDebugPrinting = isDbg }
    $ k x

withClosure :: Closure a -> (a -> TCM b) -> TCM (Closure b)
withClosure cl k = enterClosure cl $ k >=> buildClosure

mapClosure :: (a -> TCM b) -> Closure a -> TCM (Closure b)
mapClosure k cl = enterClosure cl $ k >=> buildClosure
