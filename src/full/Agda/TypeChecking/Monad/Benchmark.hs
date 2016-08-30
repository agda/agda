-- | Measure CPU time for individual phases of the Agda pipeline.

module Agda.TypeChecking.Monad.Benchmark
  ( module Agda.Benchmarking
  , B.MonadBench
  , B.getBenchmark
  , updateBenchmarkingStatus
  , B.billTo, B.billPureTo, B.billToCPS
  , B.reset
  , print
  ) where

import Prelude hiding (print)

import Agda.Benchmarking

import Agda.TypeChecking.Monad.Base
import{-# SOURCE #-} Agda.TypeChecking.Monad.Options

import qualified Agda.Utils.Benchmark as B

import Agda.Utils.Monad
import Agda.Utils.Pretty (prettyShow)

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
  b <- B.getBenchmark
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
