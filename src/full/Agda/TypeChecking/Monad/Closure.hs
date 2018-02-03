module Agda.TypeChecking.Monad.Closure where

import Control.Monad

import Agda.TypeChecking.Monad.Base
import Agda.TypeChecking.Monad.Env
import Agda.TypeChecking.Monad.State
import Agda.TypeChecking.Monad.Context
import Agda.Utils.Lens

enterClosure :: Closure a -> (a -> TCM b) -> TCM b
enterClosure (Closure sig env scope cps x) k = do
  isDbg <- view eIsDebugPrinting
  withScope_ scope
    $ locallyState stModuleCheckpoints (const cps)
    $ withEnv env{ envIsDebugPrinting = isDbg }
    $ k x

withClosure :: Closure a -> (a -> TCM b) -> TCM (Closure b)
withClosure cl k = enterClosure cl $ k >=> buildClosure

mapClosure :: (a -> TCM b) -> Closure a -> TCM (Closure b)
mapClosure k cl = enterClosure cl $ k >=> buildClosure
