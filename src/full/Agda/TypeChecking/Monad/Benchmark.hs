-- | Measure CPU time for individual phases of the Agda pipeline.

module Agda.TypeChecking.Monad.Benchmark
  ( module Agda.TypeChecking.Monad.Base.Benchmark
  , getBenchmark
  , billTo, billTop, billPureTo
  , reimburse, reimburseTop
  ) where

import qualified Control.Exception as E (evaluate)
import Control.Monad.State
import System.CPUTime

import Agda.TypeChecking.Monad.Base.Benchmark
import Agda.TypeChecking.Monad.Base
import Agda.TypeChecking.Monad.State

-- | Add CPU time to specified account.
addToAccount :: Account -> CPUTime -> TCM ()
addToAccount k v = modifyBenchmark $ addCPUTime k v

-- | Bill a computation to a specific account (True) or reimburse (False).
billTo' :: Bool -> Account -> TCM a -> TCM a
billTo' add k m = do
  start  <- liftIO $ getCPUTime
  result <- liftIO . E.evaluate =<< m
  stop   <- liftIO $ getCPUTime
  addToAccount k $ if add then stop - start else start - stop
  return result

-- | Bill a computation to a specific account.
billTo :: Account -> TCM a -> TCM a
billTo = billTo' True

-- | Bill a top account.
billTop :: Phase -> TCM a -> TCM a
billTop k = billTo [k]

-- | Bill a pure computation to a specific account.
{-# SPECIALIZE billPureTo :: Account -> a -> TCM a #-}
billPureTo :: MonadTCM tcm => Account -> a -> tcm a
billPureTo k a = liftTCM $ billTo k $ return a
-- billPureTo k a = liftTCM $ billTo k $ liftIO $ E.evaluate a

-- | Reimburse a specific account for computation costs.
reimburse :: Account -> TCM a -> TCM a
reimburse = billTo' False

-- | Reimburse a top account.
reimburseTop :: Phase -> TCM a -> TCM a
reimburseTop k = reimburse [k]

