{-# LANGUAGE FlexibleInstances         #-}
{-# LANGUAGE FunctionalDependencies    #-}
{-# LANGUAGE MultiParamTypeClasses     #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE UndecidableInstances      #-}
{-# LANGUAGE TupleSections             #-}

-- | Tools for benchmarking and accumulating results.
--   Nothing Agda-specific in here.

module Agda.Utils.Benchmark where

import Prelude hiding (null)

import qualified Control.Exception as E (evaluate)
import Control.Monad.Reader
import Control.Monad.State

import Data.Functor
import qualified Data.List as List

import qualified Text.PrettyPrint.Boxes as Boxes

import Agda.Utils.Null
import Agda.Utils.Monad hiding (finally)
import qualified Agda.Utils.Maybe.Strict as Strict
import Agda.Utils.Pretty
import Agda.Utils.Time
import Agda.Utils.Trie (Trie)
import qualified Agda.Utils.Trie as Trie


-- * Benchmark trie

-- | Account we can bill computation time to.
type Account a = [a]

-- | Record when we started billing the current account.
type CurrentAccount a = Strict.Maybe (Account a, CPUTime)

type Timings        a = Trie a CPUTime

-- | Benchmark structure is a trie, mapping accounts (phases and subphases)
--   to CPU time spent on their performance.
data Benchmark a = Benchmark
  { benchmarkOn    :: !Bool
    -- ^ Are we benchmarking at all?
  , currentAccount :: !(CurrentAccount a)
    -- ^ What are we billing to currently?
  , timings        :: !(Timings a)
    -- ^ The accounts and their accumulated timing bill.
  }

-- | Initial benchmark structure (empty).
instance Null (Benchmark a) where
  empty = Benchmark
    { benchmarkOn = False
    , currentAccount = Strict.Nothing
    , timings = empty
    }
  null = null . timings

-- | Semantic editor combinator.
mapBenchmarkOn :: (Bool -> Bool) -> Benchmark a -> Benchmark a
mapBenchmarkOn f b = b { benchmarkOn = f $ benchmarkOn b }

-- | Semantic editor combinator.
mapCurrentAccount ::
  (CurrentAccount a -> CurrentAccount a) -> Benchmark a -> Benchmark a
mapCurrentAccount f b = b { currentAccount = f (currentAccount b) }

-- | Semantic editor combinator.
mapTimings :: (Timings a -> Timings a) -> Benchmark a -> Benchmark a
mapTimings f b = b { timings = f (timings b) }

-- | Add to specified CPU time account.
addCPUTime :: Ord a => Account a -> CPUTime -> Benchmark a -> Benchmark a
addCPUTime acc t = mapTimings (Trie.insertWith (+) acc t)

-- | Print benchmark as two-column table with totals.
instance (Ord a, Pretty a) => Pretty (Benchmark a) where
  pretty b = text $ Boxes.render table
    where
    (accounts, times) = unzip $ Trie.toList $ timings b

    -- Generate a table.
    table = Boxes.hsep 1 Boxes.left [col1, col2]

    -- First column: Accounts.
    col1 = Boxes.vcat Boxes.left $
           map Boxes.text $
           "Total" : map showAccount accounts
    -- Second column: Times.
    col2 = Boxes.vcat Boxes.right $
           map (Boxes.text . prettyShow) $
           sum times : times

    showAccount [] = "Miscellaneous"
    showAccount ks = List.intercalate "." $ map prettyShow ks


-- * Benchmarking monad.

-- | Monad with access to benchmarking data.

class (Ord a, Functor m, MonadIO m) => MonadBench a m | m -> a where
  getBenchmark :: m (Benchmark a)

  getsBenchmark :: (Benchmark a -> c) -> m c
  getsBenchmark f = f <$> getBenchmark

  putBenchmark :: Benchmark a -> m ()
  putBenchmark b = modifyBenchmark $ const b

  modifyBenchmark :: (Benchmark a -> Benchmark a) -> m ()
  modifyBenchmark f = do
    b <- getBenchmark
    putBenchmark $! f b

  -- | We need to be able to terminate benchmarking in case of an exception.
  finally :: m b -> m c -> m b

-- needs UndecidableInstances because of weakness of FunctionalDependencies
instance MonadBench a m => MonadBench a (ReaderT r m) where
  getBenchmark    = lift $ getBenchmark
  putBenchmark    = lift . putBenchmark
  modifyBenchmark = lift . modifyBenchmark
  finally m f = ReaderT $ \ r ->
    finally (m `runReaderT` r) (f `runReaderT` r)

instance MonadBench a m => MonadBench a (StateT r m) where
  getBenchmark    = lift $ getBenchmark
  putBenchmark    = lift . putBenchmark
  modifyBenchmark = lift . modifyBenchmark
  finally m f = StateT $ \s ->
    finally (m `runStateT` s) (f `runStateT` s)

-- | Turn benchmarking on/off.

setBenchmarking :: MonadBench a m => Bool -> m ()
setBenchmarking b = modifyBenchmark $ mapBenchmarkOn $ const b

-- | Bill current account with time up to now.
--   Switch to new account.
--   Return old account (if any).

switchBenchmarking :: MonadBench a m
  => Strict.Maybe (Account a)      -- ^ Maybe new account.
  -> m (Strict.Maybe (Account a))  -- ^ Maybe old account.
switchBenchmarking newAccount = do
  now <- liftIO $ getCPUTime
  -- Stop and bill current benchmarking.
  oldAccount <- getsBenchmark currentAccount
  Strict.whenJust oldAccount $ \ (acc, start) ->
    modifyBenchmark $ addCPUTime acc $ now - start
  -- Switch to new account.
  modifyBenchmark $ mapCurrentAccount $ const $ (, now) <$> newAccount
  return $ fst <$> oldAccount

-- | Resets the account and the timing information.

reset :: MonadBench a m => m ()
reset = modifyBenchmark $
  mapCurrentAccount (const Strict.Nothing) .
  mapTimings (const Trie.empty)

-- | Bill a computation to a specific account.
--   Works even if the computation is aborted by an exception.

billTo :: MonadBench a m => Account a -> m c -> m c
billTo account m = ifNotM (getsBenchmark benchmarkOn) m $ do
  -- Switch to new account.
  old <- switchBenchmarking $ Strict.Just account
  -- Compute and switch back to old account.
  (liftIO . E.evaluate =<< m) `finally` switchBenchmarking old

-- | Bill a pure computation to a specific account.
billPureTo :: MonadBench a m  => Account a -> c -> m c
billPureTo account = billTo account . return
