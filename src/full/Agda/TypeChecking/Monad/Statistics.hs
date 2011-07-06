
module Agda.TypeChecking.Monad.Statistics
    ( tick, tickN, getStatistics
    ) where

import Control.Monad.State
import Data.Map as Map

import Agda.TypeChecking.Monad.Base

tick :: String -> TCM ()
tick x = tickN x 1

tickN :: String -> Integer -> TCM ()
tickN x n = modify $ \s ->
  let st' = inc $ stStatistics s in
  force st' `seq` s { stStatistics = st' }
  where
    -- We need to be strict in the map
    force m = sum (Map.elems m)
    inc = Map.insertWith (\_ m -> m + n) x n

getStatistics :: TCM Statistics
getStatistics = gets stStatistics
