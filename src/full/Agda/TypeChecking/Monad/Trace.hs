
module Agda.TypeChecking.Monad.Trace where

import Control.Monad.State

import Agda.Syntax.Position
import Agda.TypeChecking.Monad.Base
import Agda.Utils.Monad
import Agda.Utils.Trace

---------------------------------------------------------------------------
-- * Trace
---------------------------------------------------------------------------

-- | Record a function call in the trace.
traceCall :: MonadTCM tcm => (Maybe r -> Call) -> tcm r -> tcm r
traceCall mkCall m = do
    cl <- buildClosure $ mkCall Nothing
    onTrace $ newCall cl
    r <- m
    onTrace $ updateCall $ cl { clValue = mkCall (Just r) }
    return r

traceCall_ :: MonadTCM tcm => (Maybe () -> Call) -> tcm r -> tcm r
traceCall_ mkCall = traceCall (mkCall . fmap (const ()))

traceCallCPS :: MonadTCM tcm => (Maybe r -> Call) -> (r -> tcm a) -> ((r -> tcm a) -> tcm b) -> tcm b
traceCallCPS mkCall ret cc = do
    cl <- buildClosure $ mkCall Nothing
    onTrace $ newCall cl
    cc $ \r -> do
	onTrace $ updateCall $ cl { clValue = mkCall (Just r) }
	ret r

traceCallCPS_ :: MonadTCM tcm => (Maybe () -> Call) -> tcm a -> (tcm a -> tcm b) -> tcm b
traceCallCPS_ mkCall ret cc =
    traceCallCPS mkCall (const ret) (\k -> cc $ k ())

getTrace :: MonadTCM tcm => tcm CallTrace
getTrace = liftTCM $ gets stTrace

setTrace :: MonadTCM tcm => CallTrace -> tcm ()
setTrace tr = liftTCM $ modify $ \s -> s { stTrace = tr }

getCurrentRange :: MonadTCM tcm => tcm Range
getCurrentRange = getRange <$> getTrace

setCurrentRange :: MonadTCM tcm => Range -> tcm a -> tcm a
setCurrentRange r
  | r == noRange = id
  | otherwise    = traceCall (SetRange r)

onTrace :: MonadTCM tcm => (CallTrace -> CallTrace) -> tcm ()
onTrace f = do
    tr <- getTrace
    setTrace (f tr)

withTrace :: MonadTCM tcm => CallTrace -> tcm a -> tcm a
withTrace tr m = do
    tr0 <- getTrace
    setTrace tr
    x <- m
    setTrace tr0
    return x

