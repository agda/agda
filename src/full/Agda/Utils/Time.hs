{-# OPTIONS_GHC -Wunused-imports #-}

-- To avoid warning on derived Integral instance for CPUTime.
{-# OPTIONS_GHC -fno-warn-identities #-}

{-# LANGUAGE CPP #-}

-- | Time-related utilities.

module Agda.Utils.Time
  ( ClockTime
  , getClockTime
  , getCPUTime
  , measureTime
  , CPUTime(..)
  , fromMilliseconds
  , getLocalTime
  ) where

import Control.DeepSeq
import Control.Monad.Trans
import qualified System.CPUTime as CPU


import qualified Data.Time

import Agda.Syntax.Common.Pretty
import Agda.Utils.String

-- | Timestamps.

type ClockTime = Data.Time.UTCTime

-- | The current time.

getClockTime :: IO ClockTime
getClockTime = Data.Time.getCurrentTime

-- | CPU time in pico (10^-12) seconds.

newtype CPUTime = CPUTime Integer
  deriving (Eq, Show, Ord, Num, Real, Enum, Integral, NFData)

fromMilliseconds :: Integer -> CPUTime
fromMilliseconds n = CPUTime (n * 1000000000)

-- | Print CPU time in milli (10^-3) seconds.

instance Pretty CPUTime where
  pretty (CPUTime ps) =
    text $ showThousandSep (div ps 1000000000) ++ "ms"

{-# SPECIALIZE getCPUTime :: IO CPUTime #-}
getCPUTime :: MonadIO m => m CPUTime
getCPUTime = liftIO $ CPUTime <$> CPU.getCPUTime

-- | Measure the time of a computation.
--   Of course, does not work with exceptions.
measureTime :: MonadIO m => m a -> m (a, CPUTime)
measureTime m = do
  start <- liftIO $ getCPUTime
  x     <- m
  stop  <- liftIO $ getCPUTime
  return (x, stop - start)

-- | Get the current local time
getLocalTime :: IO Data.Time.LocalTime
#ifdef wasm32_HOST_ARCH
-- tzset is not available on wasm, so just default to utc instead.
getLocalTime = Data.Time.utcToLocalTime Data.Time.utc <$> Data.Time.getCurrentTime
#else
getLocalTime = liftA2 Data.Time.utcToLocalTime Data.Time.getCurrentTimeZone Data.Time.getCurrentTime
#endif
