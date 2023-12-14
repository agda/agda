
-- | Tools for benchmarking and accumulating results.
--   Nothing Agda-specific in here.

module Agda.Utils.Benchmark where

import Prelude hiding (null)

import Control.DeepSeq
import qualified Control.Exception as E (evaluate)
import Control.Monad.Except
import Control.Monad.Reader
import Control.Monad.Writer
import Control.Monad.State
import Control.Monad.IO.Class ( MonadIO(..) )


import Data.Function (on)
import qualified Data.List as List
import Data.Monoid
import Data.Maybe

import GHC.Generics (Generic)

import qualified Text.PrettyPrint.Boxes as Boxes

import Agda.Utils.ListT
import Agda.Utils.Null
import Agda.Utils.Monad hiding (finally)
import qualified Agda.Utils.Maybe.Strict as Strict
import Agda.Syntax.Common.Pretty
import Agda.Utils.Time
import Agda.Utils.Trie (Trie)
import qualified Agda.Utils.Trie as Trie


-- * Benchmark trie

-- | Account we can bill computation time to.
type Account a = [a]

-- | Record when we started billing the current account.
type CurrentAccount a = Strict.Maybe (Account a, CPUTime)

type Timings        a = Trie a CPUTime

data BenchmarkOn a = BenchmarkOff | BenchmarkOn | BenchmarkSome (Account a -> Bool)
  deriving Generic

isBenchmarkOn :: Account a -> BenchmarkOn a -> Bool
isBenchmarkOn _ BenchmarkOff      = False
isBenchmarkOn _ BenchmarkOn       = True
isBenchmarkOn a (BenchmarkSome p) = p a

-- | Benchmark structure is a trie, mapping accounts (phases and subphases)
--   to CPU time spent on their performance.
data Benchmark a = Benchmark
  { benchmarkOn    :: !(BenchmarkOn a)
    -- ^ Are we benchmarking at all?
  , currentAccount :: !(CurrentAccount a)
    -- ^ What are we billing to currently?
  , timings        :: !(Timings a)
    -- ^ The accounts and their accumulated timing bill.
  }
  deriving Generic

-- | Initial benchmark structure (empty).
instance Null (Benchmark a) where
  empty = Benchmark
    { benchmarkOn = BenchmarkOff
    , currentAccount = Strict.Nothing
    , timings = empty
    }
  null = null . timings

-- | Semantic editor combinator.
mapBenchmarkOn :: (BenchmarkOn a -> BenchmarkOn a) -> Benchmark a -> Benchmark a
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

-- | Print benchmark as three-column table with totals.
instance (Ord a, Pretty a) => Pretty (Benchmark a) where
  pretty b = text $ Boxes.render table
    where
    trie = timings b
    (accounts, times0) = unzip $ Trie.toListOrderedBy (flip compare `on` snd)
                               $ Trie.filter ((> fromMilliseconds 10) . snd)
                               $ Trie.mapSubTries (Just . aggr) trie
    times = map fst times0
    aggr t = (fromMaybe 0 $ Trie.lookup [] t, getSum $ foldMap Sum t)
    aggrTimes = do
      (a, (t, aggrT)) <- zip accounts times0
      return $ if t == aggrT || null a
               then ""
               else Boxes.text $ "(" ++ prettyShow aggrT ++ ")"

    -- Generate a table.
    table = Boxes.hsep 1 Boxes.left [col1, col2, col3]

    -- First column: Accounts.
    col1 = Boxes.vcat Boxes.left $
           map Boxes.text $
           "Total" : map showAccount accounts
    -- Second column: Times.
    col2 = Boxes.vcat Boxes.right $
           map (Boxes.text . prettyShow) $
           sum times : times
    -- Thid column: Aggregate times.
    col3 = Boxes.vcat Boxes.right $
           "" : aggrTimes

    showAccount [] = "Miscellaneous"
    showAccount ks = List.intercalate "." $ map prettyShow ks


-- * Benchmarking monad.

-- | Monad with access to benchmarking data.

class (Ord (BenchPhase m), Functor m, MonadIO m) => MonadBench m where
  type BenchPhase m
  getBenchmark :: m (Benchmark (BenchPhase m))

  putBenchmark :: Benchmark (BenchPhase m) -> m ()
  putBenchmark b = modifyBenchmark $ const b

  modifyBenchmark :: (Benchmark (BenchPhase m) -> Benchmark (BenchPhase m)) -> m ()
  modifyBenchmark f = do
    b <- getBenchmark
    putBenchmark $! f b

  -- | We need to be able to terminate benchmarking in case of an exception.
  finally :: m b -> m c -> m b

getsBenchmark :: MonadBench m => (Benchmark (BenchPhase m) -> c) -> m c
getsBenchmark f = f <$> getBenchmark

instance MonadBench m => MonadBench (ReaderT r m) where
  type BenchPhase (ReaderT r m) = BenchPhase m
  getBenchmark    = lift $ getBenchmark
  putBenchmark    = lift . putBenchmark
  modifyBenchmark = lift . modifyBenchmark
  finally m f = ReaderT $ \ r ->
    finally (m `runReaderT` r) (f `runReaderT` r)

instance (MonadBench m, Monoid w) => MonadBench (WriterT w m) where
  type BenchPhase (WriterT w m) = BenchPhase m
  getBenchmark    = lift $ getBenchmark
  putBenchmark    = lift . putBenchmark
  modifyBenchmark = lift . modifyBenchmark
  finally m f = WriterT $ finally (runWriterT m) (runWriterT f)

instance MonadBench m => MonadBench (StateT r m) where
  type BenchPhase (StateT r m) = BenchPhase m

  getBenchmark    = lift $ getBenchmark
  putBenchmark    = lift . putBenchmark
  modifyBenchmark = lift . modifyBenchmark
  finally m f = StateT $ \s ->
    finally (m `runStateT` s) (f `runStateT` s)

instance MonadBench m => MonadBench (ExceptT e m) where
  type BenchPhase (ExceptT e m) = BenchPhase m

  getBenchmark    = lift $ getBenchmark
  putBenchmark    = lift . putBenchmark
  modifyBenchmark = lift . modifyBenchmark
  finally m f = ExceptT $ finally (runExceptT m) (runExceptT f)

instance MonadBench m => MonadBench (ListT m) where
  type BenchPhase (ListT m) = BenchPhase m

  getBenchmark    = lift getBenchmark
  putBenchmark    = lift . putBenchmark
  modifyBenchmark = lift . modifyBenchmark
  finally m f = ListT $ finally (runListT m) (runListT f)

-- | Turn benchmarking on/off.

setBenchmarking :: MonadBench m => BenchmarkOn (BenchPhase m) -> m ()
setBenchmarking b = modifyBenchmark $ mapBenchmarkOn $ const b

-- | Bill current account with time up to now.
--   Switch to new account.
--   Return old account (if any).

switchBenchmarking :: MonadBench m
  => Strict.Maybe (Account (BenchPhase m))      -- ^ Maybe new account.
  -> m (Strict.Maybe (Account (BenchPhase m)))  -- ^ Maybe old account.
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

reset :: MonadBench m => m ()
reset = modifyBenchmark $
  mapCurrentAccount (const Strict.Nothing) .
  mapTimings (const Trie.empty)

{-# INLINABLE billTo #-}
-- | Bill a computation to a specific account.
--   Works even if the computation is aborted by an exception.

billTo :: MonadBench m => Account (BenchPhase m) -> m c -> m c
billTo account m = ifNotM (isBenchmarkOn account <$> getsBenchmark benchmarkOn) m $ do
  -- Switch to new account.
  old <- switchBenchmarking $ Strict.Just account
  -- Compute and switch back to old account.
  (liftIO . E.evaluate =<< m) `finally` switchBenchmarking old

-- | Bill a CPS function to an account. Can't handle exceptions.
billToCPS :: MonadBench m => Account (BenchPhase m) -> ((b -> m c) -> m c) -> (b -> m c) -> m c
billToCPS account f k = ifNotM (isBenchmarkOn account <$> getsBenchmark benchmarkOn) (f k) $ do
  -- Switch to new account.
  old <- switchBenchmarking $ Strict.Just account
  f $ \ x -> x `seq` do
    _ <- switchBenchmarking old
    k x

-- | Bill a pure computation to a specific account.
billPureTo :: MonadBench m  => Account (BenchPhase m) -> c -> m c
billPureTo account = billTo account . return

-- NFData instances.

instance NFData a => NFData (BenchmarkOn a)
instance NFData a => NFData (Benchmark a)
