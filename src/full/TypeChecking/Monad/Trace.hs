
module TypeChecking.Monad.Trace where

import Control.Monad.Reader

import Syntax.Position
import TypeChecking.Monad.Base
import Utils.Monad

---------------------------------------------------------------------------
-- * Trace
---------------------------------------------------------------------------

getTrace :: TCM Trace
getTrace = asks envTrace

-- setCurrentRange :: HasRange a => a -> TCM ()
-- setCurrentRange x = modify $ \s -> s { envTrace = (envTrace s) { traceRange = getRange x } }

getCurrentRange :: TCM Range
getCurrentRange = getRange <$> getTrace

onTrace :: (Trace -> Trace) -> TCM a -> TCM a
onTrace f = local $ \e -> e { envTrace = f $ envTrace e }

withRange :: HasRange a => a -> TCM b -> TCM b
withRange x = onTrace $ \t -> t { traceRange = getRange x }

-- withRange :: Range -> TCM a -> TCM a
-- withRange r m =
--     do	r0 <- getCurrentRange
-- 	setCurrentRange r
-- 	x <- m
-- 	setCurrentRange r0
-- 	return x



