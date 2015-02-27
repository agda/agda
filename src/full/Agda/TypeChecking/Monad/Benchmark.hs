{-# LANGUAGE CPP #-}

-- | Measure CPU time for individual phases of the Agda pipeline.

module Agda.TypeChecking.Monad.Benchmark
  ( module Agda.TypeChecking.Monad.Base.Benchmark
  , getBenchmark
  , benchmarking
  , billTo, billPureTo
  , print
  ) where

import qualified Control.Exception as E (evaluate)
import Control.Monad.State
import Data.List
import Prelude hiding (print)
import qualified Text.PrettyPrint.Boxes as Boxes

import Agda.TypeChecking.Monad.Base.Benchmark
import Agda.TypeChecking.Monad.Base
import{-# SOURCE #-} Agda.TypeChecking.Monad.Options
import Agda.TypeChecking.Monad.State

import qualified Agda.Utils.Maybe.Strict as Strict
import Agda.Utils.Monad
import Agda.Utils.Pretty (prettyShow)
import Agda.Utils.Time
import qualified Agda.Utils.Trie as Trie

#include "undefined.h"
import Agda.Utils.Impossible

benchmarkKey :: String
benchmarkKey = "profile"

benchmarkLevel :: Int
benchmarkLevel = 7

-- | Check whether benchmarking is activated.
{-# SPECIALIZE benchmarking :: TCM Bool #-}
benchmarking :: MonadTCM tcm => tcm Bool
benchmarking = liftTCM $ hasVerbosity benchmarkKey benchmarkLevel

-- | Prints the accumulated benchmark results. Does nothing if
-- profiling is not activated at level 7.
print :: MonadTCM tcm => tcm ()
print = liftTCM $ whenM benchmarking $ do

  (accounts, times) <- unzip . Trie.toList . timings <$> getBenchmark

  -- Generate a table.
  let -- First column: Accounts.
      col1 = Boxes.vcat Boxes.left $
             map Boxes.text $
             "Total" : map showAccount accounts
      -- Second column: Times.
      col2 = Boxes.vcat Boxes.right $
             map (Boxes.text . prettyShow) $
             sum times : times
      table = Boxes.hsep 1 Boxes.left [col1, col2]
  reportSLn benchmarkKey benchmarkLevel $
    Boxes.render table

  where
  showAccount [] = "Miscellaneous"
  showAccount ks = intercalate "." (map show ks)

-- | Add CPU time to specified account.
addToAccount :: Account -> CPUTime -> TCM ()
addToAccount k v = modifyBenchmark $ addCPUTime k v

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
