
module TypeChecking.Monad.Trace where

import Control.Monad.State

import Syntax.Position
import TypeChecking.Monad.Base
import Utils.Monad
import Utils.Trace

---------------------------------------------------------------------------
-- * Trace
---------------------------------------------------------------------------

-- | Record a function call in the trace.
traceCall :: (Maybe r -> Call) -> TCM r -> TCM r
traceCall mkCall m = do
    cl <- buildClosure $ mkCall Nothing
    onTrace $ newCall cl
    r <- m
    onTrace $ updateCall $ cl { clValue = mkCall (Just r) }
    return r

traceCall_ :: (Maybe () -> Call) -> TCM r -> TCM r
traceCall_ mkCall = traceCall (mkCall . fmap (const ()))

traceCallCPS :: (Maybe r -> Call) -> (r -> TCM a) -> ((r -> TCM a) -> TCM b) -> TCM b
traceCallCPS mkCall ret cc = do
    cl <- buildClosure $ mkCall Nothing
    onTrace $ newCall cl
    cc $ \r -> do
	onTrace $ updateCall $ cl { clValue = mkCall (Just r) }
	ret r

traceCallCPS_ :: (Maybe () -> Call) -> TCM a -> (TCM a -> TCM b) -> TCM b
traceCallCPS_ mkCall ret cc =
    traceCallCPS mkCall (const ret) (\k -> cc $ k ())

getTrace :: TCM CallTrace
getTrace = gets stTrace

setTrace :: CallTrace -> TCM ()
setTrace tr = modify $ \s -> s { stTrace = tr }

getCurrentRange :: TCM Range
getCurrentRange = getRange <$> getTrace

onTrace :: (CallTrace -> CallTrace) -> TCM ()
onTrace f = do
    tr <- getTrace
    setTrace (f tr)

withTrace :: CallTrace -> TCM a -> TCM a
withTrace tr m = do
    tr0 <- getTrace
    setTrace tr
    x <- m
    setTrace tr0
    return x

