-- | Benchmark pure and IO computations.

module Agda.Utils.Benchmark where

import qualified Control.Exception as E (evaluate)

import Data.IORef

import System.IO.Unsafe

import Agda.Utils.Pretty
import Agda.Utils.Time
import Agda.Utils.Trie

type Benchmarks = CPUTime

{-# NOINLINE benchmarks #-}
benchmarks :: IORef Benchmarks
benchmarks = unsafePerformIO $ newIORef 0

modifyBenchmarks :: (Benchmarks -> Benchmarks) -> IO ()
modifyBenchmarks f = do
  x <- readIORef benchmarks
  writeIORef benchmarks $! f x

benchmark :: IO a -> IO a
benchmark m = do
  (x, t) <- measureTime $ E.evaluate =<< m
  modifyBenchmarks (t +)
  return x

benchmarkPure :: a -> a
benchmarkPure a = unsafePerformIO $ benchmark $ return a

print :: IO ()
print = do
  t <- readIORef benchmarks
  putStrLn $ "Time spent on non-TCM benchmarks: " ++ prettyShow t
