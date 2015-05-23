{-# LANGUAGE CPP,
             FlexibleInstances,
             MultiParamTypeClasses,
             TypeSynonymInstances,
             UndecidableInstances #-}

#if __GLASGOW_HASKELL__ <= 708
{-# LANGUAGE OverlappingInstances #-}
#endif

-- | Measure CPU time for individual phases of the Agda pipeline.

module Agda.TypeChecking.Monad.Benchmark
  ( module Agda.Benchmarking
  , MonadBench
  , getBenchmark
  , updateBenchmarkingStatus
  , billTo, billPureTo
  , print
  ) where

import Prelude hiding (print)

import qualified Control.Exception as E (evaluate)
import Control.Monad.State

import Data.List

import qualified Text.PrettyPrint.Boxes as Boxes

import Agda.Benchmarking

import Agda.TypeChecking.Monad.Base as TCM
import{-# SOURCE #-} Agda.TypeChecking.Monad.Options
import qualified Agda.TypeChecking.Monad.State as TCState

import Agda.Utils.Benchmark (MonadBench(..), billTo, billPureTo)
import qualified Agda.Utils.Benchmark as B

import Agda.Utils.Monad
import Agda.Utils.Pretty (prettyShow)

#include "undefined.h"
import Agda.Utils.Impossible

-- Select one of the following two instances.
-- For Benchmarking.billToPure to work, only the IORef alternative works.

-- | We store benchmark statistics in an IORef.
--   This enables benchmarking pure computation, see
--   ''Agda.Benchmarking''.
instance MonadBench Phase TCM where
-- instance MonadTCM tcm => MonadBench Phase tcm where
  getBenchmark = liftIO $ getBenchmark
  putBenchmark = liftIO . putBenchmark
  finally = TCM.finally_

-- -- | We store benchmark statistics in the TCM.
-- instance MonadBench Phase TCM where
--   getBenchmark    = TCState.getBenchmark
--   modifyBenchmark = TCState.modifyBenchmark
--   finally = TCM.finally_
-- -- instance MonadTCM tcm => MonadBench Phase tcm where
-- --   getBenchmark    = liftTCM $ TCState.getBenchmark
-- --   modifyBenchmark = liftTCM . TCState.modifyBenchmark

benchmarkKey :: String
benchmarkKey = "profile"

benchmarkLevel :: Int
benchmarkLevel = 7

-- | When verbosity is set or changes, we need to turn benchmarking on or off.
updateBenchmarkingStatus :: TCM ()
-- {-# SPECIALIZE updateBenchmarkingStatus :: TCM () #-}
-- updateBenchmarkingStatus :: (HasOptions m, MonadBench a m) => m ()
updateBenchmarkingStatus =
  B.setBenchmarking =<< hasVerbosity benchmarkKey benchmarkLevel

-- | Check whether benchmarking is activated.
{-# SPECIALIZE benchmarking :: TCM Bool #-}
benchmarking :: MonadTCM tcm => tcm Bool
benchmarking = liftTCM $ hasVerbosity benchmarkKey benchmarkLevel

-- | Prints the accumulated benchmark results. Does nothing if
-- profiling is not activated at level 7.
print :: MonadTCM tcm => tcm ()
print = liftTCM $ whenM benchmarking $ do
  b <- getBenchmark
  reportSLn benchmarkKey benchmarkLevel $ prettyShow b

-- -- | Bill a computation to a specific account.
-- {-# SPECIALIZE billTo :: Account -> TCM a -> TCM a #-}
-- billTo :: MonadTCM tcm => Account -> tcm a -> tcm a
-- billTo account = lift1TCM $ B.billTo account
   -- Andreas, 2015-05-23
   -- FAILS as lift1TCM :: (TCM a -> TCM b) -> tcm a -> tcm b
   -- cannot be implemented lazily in general.
   -- With `lazily` I mean that embedded IO computations in @tcm a@ are
   -- not executed, but passed on to @TCM a -> TCM b@ unevaluated.
   -- If they are treated strictly, then the whole benchmarking is inaccurate
   -- of course, as the computation is done before the clock is started.

-- -- | Bill a pure computation to a specific account.
-- {-# SPECIALIZE billPureTo :: Account -> a -> TCM a #-}
-- billPureTo :: MonadTCM tcm => Account -> a -> tcm a
-- billPureTo k a = billTo k $ return a
