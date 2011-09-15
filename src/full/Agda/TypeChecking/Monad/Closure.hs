
module Agda.TypeChecking.Monad.Closure where

import Agda.TypeChecking.Monad.Base
import Agda.TypeChecking.Monad.Env
import Agda.TypeChecking.Monad.State
import Agda.TypeChecking.Monad.Signature
import Agda.TypeChecking.Monad.Trace

enterClosure :: Closure a -> (a -> TCM b) -> TCM b
enterClosure (Closure sig env scope x) k =
    withScope_ scope
    $ withEnv env
    $ k x
