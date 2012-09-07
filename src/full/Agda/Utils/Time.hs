{-# LANGUAGE CPP #-}

-- | Time-related utilities.

module Agda.Utils.Time
  ( ClockTime
  , getClockTime
  ) where

#if MIN_VERSION_directory(1,1,1)
import qualified Data.Time
#else
import qualified System.Time
#endif

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
