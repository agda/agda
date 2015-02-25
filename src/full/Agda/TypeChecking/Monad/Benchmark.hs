{-# LANGUAGE CPP #-}

-- | Measure CPU time for individual phases of the Agda pipeline.

module Agda.TypeChecking.Monad.Benchmark
  ( module Agda.TypeChecking.Monad.Base.Benchmark
  , getBenchmark
  , benchmarking, reportBenchmarkingLn, reportBenchmarkingDoc
  , billTo, billPureTo
  ) where

import qualified Control.Exception as E (evaluate)
import Control.Monad.State

import Agda.TypeChecking.Monad.Base.Benchmark
import Agda.TypeChecking.Monad.Base
import{-# SOURCE #-} Agda.TypeChecking.Monad.Options
import Agda.TypeChecking.Monad.State

import qualified Agda.Utils.Maybe.Strict as Strict
import Agda.Utils.Monad
import Agda.Utils.Pretty (Doc)
import Agda.Utils.Time

#include "undefined.h"
import Agda.Utils.Impossible

-- | Check whether benchmarking is activated.
{-# SPECIALIZE benchmarking :: TCM Bool #-}
benchmarking :: MonadTCM tcm => tcm Bool
benchmarking = liftTCM $ hasVerbosity "profile" 7

-- | Report benchmarking results.
reportBenchmarkingLn :: String -> TCM ()
reportBenchmarkingLn = reportSLn "profile" 7

-- | Report benchmarking results.
reportBenchmarkingDoc :: TCM Doc -> TCM ()
reportBenchmarkingDoc = reportSDoc "profile" 7

-- | Bill a computation to a specific account.
billTo :: MonadTCM tcm => Account -> tcm a -> tcm a
billTo account m = ifNotM benchmarking m {- else -} $ do
  oldAccount <- liftTCM $ do
    oldAccount <- currentAccount <$> liftTCM getBenchmark
    modifyBenchmark $ modifyCurrentAccount $ const (Strict.Just account)
    return oldAccount
  (res, time) <- measureTime $ liftIO . E.evaluate =<< m
  liftTCM $ do
    addToAccount account time
    case oldAccount of
      Strict.Just acc -> addToAccount acc (- time)
      Strict.Nothing  -> return ()
    modifyBenchmark $ modifyCurrentAccount $ const oldAccount
  return res

-- | Bill a pure computation to a specific account.
{-# SPECIALIZE billPureTo :: Account -> a -> TCM a #-}
billPureTo :: MonadTCM tcm => Account -> a -> tcm a
billPureTo k a = billTo k $ return a

-- * Auxiliary functions

-- | Add CPU time to specified account.
addToAccount :: Account -> CPUTime -> TCM ()
addToAccount k v = modifyBenchmark $ addCPUTime k v
