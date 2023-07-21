{-# OPTIONS_GHC -Wunused-imports #-}

-- | Measure CPU time for individual phases of the Agda pipeline.

module Agda.TypeChecking.Monad.Benchmark
  ( module Agda.Benchmarking
  , B.MonadBench
  , B.BenchPhase
  , B.getBenchmark
  , updateBenchmarkingStatus
  , B.billTo, B.billPureTo, B.billToCPS
  , B.reset
  , print
  ) where

import Prelude hiding (print)

import Agda.Benchmarking

import Agda.TypeChecking.Monad.Base
import Agda.TypeChecking.Monad.Debug

import qualified Agda.Utils.Benchmark as B

import Agda.Utils.Monad
import Agda.Utils.Pretty (prettyShow)
import qualified Agda.Utils.ProfileOptions as Profile

-- | When profile options are set or changed, we need to turn benchmarking on or off.
updateBenchmarkingStatus :: TCM ()
-- {-# SPECIALIZE updateBenchmarkingStatus :: TCM () #-}
-- updateBenchmarkingStatus :: (HasOptions m, MonadBench a m) => m ()
updateBenchmarkingStatus =
  B.setBenchmarking =<< benchmarking

-- | Check whether benchmarking is activated.
{-# SPECIALIZE benchmarking :: TCM (B.BenchmarkOn Phase) #-}
benchmarking :: MonadTCM tcm => tcm (B.BenchmarkOn Phase)
benchmarking = liftTCM $
  ifM (hasProfileOption Profile.Internal)    (pure $ B.BenchmarkSome isInternalAccount) $
  ifM (hasProfileOption Profile.Definitions) (pure $ B.BenchmarkSome isDefAccount) $
  ifM (hasProfileOption Profile.Modules)     (pure $ B.BenchmarkSome isModuleAccount) $
  pure B.BenchmarkOff

-- | Prints the accumulated benchmark results. Does nothing if
--   no benchmark profiling is enabled.
print :: MonadTCM tcm => tcm ()
print = liftTCM $ whenM (B.isBenchmarkOn [] <$> benchmarking) $ do
  b <- B.getBenchmark
  -- Andreas, 2017-07-29, issue #2602:
  -- The following line messes up the AgdaInfo buffer,
  -- thus, as Fredrik Forsberg suggest, I restore the original
  -- line for release 2.5.3 until a fix is found.
  -- reportSLn "" 0 $ prettyShow b
  -- Ulf, 2020-03-04: Using benchmarkLevel here means that it only prints if internal benchmarking
  -- is turned on, effectively making module/definition benchmarking impossible (since internal
  -- takes precedence). It needs to be > 1 to avoid triggering #2602 though. Also use
  -- displayDebugMessage instead of reportSLn to avoid requiring -v profile:2.
  displayDebugMessage "profile" 2 $ prettyShow b

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
