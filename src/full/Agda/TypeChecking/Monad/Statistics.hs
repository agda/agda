{-# OPTIONS_GHC -fwarn-missing-signatures #-}

-- | Collect statistics.

module Agda.TypeChecking.Monad.Statistics
    ( tick, tickN, tickMax, getStatistics
    ) where

import Control.Monad.State
import Data.Map as Map

import Agda.TypeChecking.Monad.Base

-- | Get the statistics.
getStatistics :: TCM Statistics
getStatistics = gets stStatistics

-- | Modify the statistics via given function.
modifyStatistics :: (Statistics -> Statistics) -> TCM ()
modifyStatistics f = modify $ \ s -> s { stStatistics = f (stStatistics s) }

-- | Increase specified counter by @1@.
tick :: String -> TCM ()
tick x = tickN x 1

-- | Increase specified counter by @n@.
tickN :: String -> Integer -> TCM ()
tickN s n = modifyCounter s (n +)

-- | Set the specified counter to the maximum of its current value and @n@.
tickMax :: String -> Integer -> TCM ()
tickMax s n = modifyCounter s (max n)

-- | Modify specified counter by a function @f@.
modifyCounter :: String -> (Integer -> Integer) -> TCM ()
modifyCounter x f = modifyStatistics $ force . update
  where
    -- We need to be strict in the map.
    -- Andreas, 2014-03-22:  Could we take Data.Map.Strict instead of this hack?
    -- Or force the map by looking up the very element we inserted?
    -- force m = Map.lookup x m `seq` m
    -- Or use insertLookupWithKey?
    -- update m = old `seq` m' where
    --   (old, m') = Map.insertLookupWithKey (\ _ new old -> f old) x dummy m
    force m = sum (Map.elems m) `seq` m
    update  = Map.insertWith (\ new old -> f old) x dummy
    dummy   = f 0

