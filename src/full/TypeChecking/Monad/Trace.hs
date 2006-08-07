
module TypeChecking.Monad.Trace where

import Control.Monad.State

import Syntax.Position
import TypeChecking.Monad.Base
import TypeChecking.Monad.Closure
import Utils.Monad

---------------------------------------------------------------------------
-- * Trace
---------------------------------------------------------------------------

newCall :: Closure Call -> Trace -> Trace
newCall c (TopLevel cs)	       = Current c NoParent cs []
newCall c (Current c' p ss cs) = Current c (Parent c' p ss) cs []

updateCall :: Closure Call -> Trace -> Trace
updateCall c (TopLevel _)	 = error $ "updateCall: no call in progress"
updateCall c (Current _ p ss cs) = case p of
    NoParent	     -> TopLevel $ Child c cs : ss
    Parent c' p' ss' -> Current c' p' ss' $ Child c cs : ss

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

getTrace :: TCM Trace
getTrace = gets stTrace

setTrace :: Trace -> TCM ()
setTrace tr = modify $ \s -> s { stTrace = tr }

-- setCurrentRange :: HasRange a => a -> TCM ()
-- setCurrentRange x = modify $ \s -> s { stTrace = (stTrace s) { traceRange = getRange x } }

getCurrentRange :: TCM Range
getCurrentRange = getRange <$> getTrace

onTrace :: (Trace -> Trace) -> TCM ()
onTrace f = do
    tr <- getTrace
    setTrace (f tr)

withTrace :: (Trace -> Trace) -> TCM a -> TCM a
withTrace f m = do
    tr <- getTrace
    setTrace (f tr)
    x <- m
    setTrace tr
    return x

-- withRange :: HasRange a => a -> TCM b -> TCM b
-- withRange x = onTrace $ \t -> t { traceRange = getRange x }

