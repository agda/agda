{-# LANGUAGE CPP #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}

-- To avoid warning on derived Integral instance for CPUTime.
{-# OPTIONS_GHC -fno-warn-identities #-}

-- | Time-related utilities.

module Agda.Utils.Time
  ( ClockTime
  , getClockTime
  , measureTime
  , CPUTime(..)
  ) where

import Control.Monad.Trans
import System.CPUTime

#if MIN_VERSION_directory(1,1,1)
import qualified Data.Time
#else
import qualified System.Time
#endif

import Agda.Utils.Pretty
import Agda.Utils.String

-- | Timestamps.

type ClockTime =
#if MIN_VERSION_directory(1,1,1)
  Data.Time.UTCTime
#else
  System.Time.ClockTime
#endif

-- | The current time.

getClockTime :: IO ClockTime
getClockTime =
#if MIN_VERSION_directory(1,1,1)
  Data.Time.getCurrentTime
#else
  System.Time.getClockTime
#endif

-- | CPU time in pico (10^-12) seconds.

newtype CPUTime = CPUTime Integer
  deriving (Eq, Show, Ord, Num, Real, Enum, Integral)

-- | Print CPU time in milli (10^-3) seconds.

instance Pretty CPUTime where
  pretty (CPUTime ps) =
    text $ showThousandSep (div ps 1000000000) ++ "ms"

-- | Measure the time of a computation. Returns the
measureTime :: MonadIO m => m a -> m (a, CPUTime)
measureTime m = do
  start <- liftIO $ getCPUTime
  x     <- m
  stop  <- liftIO $ getCPUTime
  return (x, CPUTime $ stop - start)
