
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

setCurrentRange :: HasRange a => a -> TCM ()
setCurrentRange x = modify $ \s -> s { stTrace = (stTrace s) { traceRange = getRange x } }

getCurrentRange :: TCM Range
getCurrentRange = getRange <$> getTrace

withRange :: Range -> TCM a -> TCM a
withRange r m =
    do	r0 <- getCurrentRange
	setCurrentRange r
	x <- m
	setCurrentRange r0
	return x



