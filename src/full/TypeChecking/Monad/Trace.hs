
module TypeChecking.Monad.Trace where

import Control.Monad.State

import Syntax.Position
import TypeChecking.Monad.Base
import Utils.Monad

---------------------------------------------------------------------------
-- * Trace
---------------------------------------------------------------------------

getTrace :: TCM Trace
getTrace = gets stTrace

setTrace :: Trace -> TCM ()
setTrace tr = modify $ \s -> s { stTrace = tr }

setCurrentRange :: HasRange a => a -> TCM ()
setCurrentRange x = modify $ \s -> s { stTrace = (stTrace s) { traceRange = getRange x } }

getCurrentRange :: TCM Range
getCurrentRange = getRange <$> getTrace

onTrace :: (Trace -> Trace) -> TCM a -> TCM a
onTrace f m = do
    tr <- getTrace
    setTrace (f tr)
    x <- m
    setTrace tr
    return x

withRange :: HasRange a => a -> TCM b -> TCM b
withRange x = onTrace $ \t -> t { traceRange = getRange x }

