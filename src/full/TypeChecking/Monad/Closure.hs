
module TypeChecking.Monad.Closure where

import TypeChecking.Monad.Base
import TypeChecking.Monad.Env
import TypeChecking.Monad.State
import TypeChecking.Monad.Signature

buildClosure :: a -> TCM (Closure a)
buildClosure x = do
    env   <- getEnv
    sig   <- getSignature
    scope <- getScope
    return $ Closure sig env scope x

enterClosure :: Closure a -> (a -> TCM b) -> TCM b
enterClosure (Closure sig env scope x) k =
    withScope scope
    $ withSignature sig
    $ withEnv env
    $ k x
    

