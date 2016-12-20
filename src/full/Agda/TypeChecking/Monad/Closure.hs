module Agda.TypeChecking.Monad.Closure where

import Control.Monad

import Agda.TypeChecking.Monad.Base
import Agda.TypeChecking.Monad.Env
import Agda.TypeChecking.Monad.State
import Agda.TypeChecking.Monad.Context

enterClosure :: Closure a -> (a -> TCM b) -> TCM b
enterClosure (Closure sig env scope pars x) k =
    withScope_ scope
    $ withEnv env
    $ withModuleParameters pars
    $ k x

withClosure :: Closure a -> (a -> TCM b) -> TCM (Closure b)
withClosure cl k = enterClosure cl $ k >=> buildClosure

mapClosure :: (a -> TCM b) -> Closure a -> TCM (Closure b)
mapClosure k cl = enterClosure cl $ k >=> buildClosure
