{-# OPTIONS_GHC -Wunused-imports #-}
{-# LANGUAGE NumDecimals #-}

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

import Data.Foldable (foldMap')
import Data.Function (on)
import Data.Maybe (fromMaybe, mapMaybe)
import Data.Monoid (Sum(..), getSum)
import qualified Data.Text.Lazy as TL

import Agda.Benchmarking
import Agda.Interaction.Options.Types( optParallelChecking, Parallelism(..) )

import Agda.TypeChecking.Monad.Base
import Agda.TypeChecking.Monad.Debug
import Agda.TypeChecking.Monad.Imports (getVisitedModule)

import qualified Agda.Utils.Benchmark as B
import qualified Agda.Utils.Trie as Trie
import Agda.Utils.Impossible (__IMPOSSIBLE__)
import Agda.Utils.Monad
import Agda.Utils.Time (CPUTime(..), fromMilliseconds)
import Agda.Syntax.Common.Pretty
  ( Doc, Pretty, comma, hsep, nest, parens, pretty, prettyShow
  , text, vcat, (<+>), ($+$)
  )
import qualified Agda.Interaction.Options.ProfileOptions as Profile

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
  extra <- ifM moduleThroughputEnabled
    (moduleThroughputDoc b)
    (pure mempty)
  -- Andreas, 2017-07-29, issue #2602:
  -- The following line messes up the AgdaInfo buffer,
  -- thus, as Fredrik Forsberg suggest, I restore the original
  -- line for release 2.5.3 until a fix is found.
  -- reportSLn "" 0 $ prettyShow b
  -- Ulf, 2020-03-04: Using benchmarkLevel here means that it only prints if internal benchmarking
  -- is turned on, effectively making module/definition benchmarking impossible (since internal
  -- takes precedence). It needs to be > 1 to avoid triggering #2602 though. Also use
  -- displayDebugMessage instead of reportSLn to avoid requiring -v profile:2.
  displayDebugMessage "profile" 2 $ pretty b $+$ extra

moduleThroughputEnabled :: TCM Bool
moduleThroughputEnabled = do
  modulesProfiling <- hasProfileOption Profile.Modules
  sequential       <- sequentialTypeChecking
  pure $ modulesProfiling && sequential

sequentialTypeChecking :: TCM Bool
sequentialTypeChecking = do
  opts <- commandLineOptions
  pure $ case optParallelChecking opts of
    Sequential -> True
    Parallel{} -> False

data ModuleThroughput = ModuleThroughput
  { mtModuleName :: TopLevelModuleName
  , mtLineCount  :: Int
  , mtTime       :: CPUTime
  }

instance Pretty ModuleThroughput where
  pretty mt =
    text (prettyShow $ mtModuleName mt) <+>
    parens
      (hsep
        [ (text (show (mtLineCount mt)) <+> "lines") <> comma
        , text (show (linesPerSecond mt)) <+> "lines/s"
        ])

moduleThroughputDoc :: Benchmark -> TCM Doc
moduleThroughputDoc b = do
  stats <- mapM loadModuleThroughput (moduleRows b)
  pure $ renderModuleThroughput stats

renderModuleThroughput :: [ModuleThroughput] -> Doc
renderModuleThroughput [] = mempty
renderModuleThroughput stats =
  vcat
    [ mempty
    , mempty
    , text "Module throughput:"
    , vcat $ map (nest 2 . pretty) stats
    ]

-- | Keep only benchmark entries corresponding to top-level modules,
--   using the aggregate module time.
moduleRows :: Benchmark -> [(TopLevelModuleName, CPUTime)]
moduleRows =
  mapMaybe moduleRow . orderedBenchmarkEntries
  where
    moduleRow (acc, (_selfTime, totalTime)) =
      case acc of
        [TopModule m] -> Just (m, totalTime)
        _             -> Nothing

-- | Flatten benchmark timings into entries ordered by aggregate time,
--   skipping entries with aggregate time below 10 ms.
--   Each entry stores:
--   * the account path
--   * time stored at this node
--   * the aggregate time of the whole subtree
orderedBenchmarkEntries :: Benchmark -> [(Account, (CPUTime, CPUTime))]
orderedBenchmarkEntries =
  Trie.toListOrderedBy (flip compare `on` snd)
  . Trie.filter ((> fromMilliseconds 10) . snd)
  . Trie.mapSubTries (Just . aggregateNode)
  . B.timings

-- | For a benchmark trie node, return:
--   * time stored at this node
--   * the aggregate time of the whole subtree
aggregateNode :: Ord a => Trie.Trie a CPUTime -> (CPUTime, CPUTime)
aggregateNode t =
  ( fromMaybe 0 $ Trie.lookup [] t
  , getSum $ foldMap' Sum t
  )

loadModuleThroughput
  :: (TopLevelModuleName, CPUTime)
  -> TCM ModuleThroughput
loadModuleThroughput (mName, totalTime) = do
  mi <- getVisitedModule mName >>= \case
    Just mi -> pure mi
    -- Module throughput is rendered only for modules already present in the benchmark output,
    -- so the corresponding module info should already be in the visited-module cache.
    Nothing -> __IMPOSSIBLE__
  let lineCount = length (lines (TL.unpack (iSource (miInterface mi))))
  pure ModuleThroughput
    { mtModuleName = mName
    , mtTime = totalTime
    , mtLineCount = lineCount
    }

picosecondsPerSecond :: Integer
picosecondsPerSecond = 1e12

linesPerSecond :: ModuleThroughput -> Integer
linesPerSecond ModuleThroughput{ mtLineCount, mtTime = CPUTime ps }
  | ps == 0   = 0
  | otherwise = round throughput
  where
    elapsedSeconds =
      fromInteger ps / fromInteger picosecondsPerSecond
    throughput =
      fromIntegral mtLineCount / elapsedSeconds

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
