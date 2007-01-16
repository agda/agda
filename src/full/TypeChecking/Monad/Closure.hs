
module TypeChecking.Monad.Closure where

import TypeChecking.Monad.Base
import TypeChecking.Monad.Env
import TypeChecking.Monad.State
import TypeChecking.Monad.Signature
import TypeChecking.Monad.Trace

enterClosure :: MonadTCM tcm => Closure a -> (a -> tcm b) -> tcm b
enterClosure (Closure sig env scope trace x) k =
    withScope scope
    $ withSignature sig
    $ withEnv env
    $ withTrace trace
    $ k x
    

