
module Agda.TypeChecking.Monad.Statistics
    ( tick, tickN, tickMax, getStatistics
    ) where

import Control.Monad.State
import Data.Map as Map

import Agda.TypeChecking.Monad.Base

tick :: String -> TCM ()
tick x = tickN x 1

tickN :: String -> Integer -> TCM ()
tickN s n = tick' s (n +)

tick' :: String -> (Integer -> Integer) -> TCM ()
tick' x f = modify $ \s ->
  let st' = upd $ stStatistics s in
  force st' `seq` s { stStatistics = st' }
  where
    -- We need to be strict in the map
    force m = sum (Map.elems m)
    upd = Map.insertWith (\_ m -> f m) x (f 0)

tickMax :: String -> Integer -> TCM ()
tickMax s n = tick' s (max n)

getStatistics :: TCM Statistics
getStatistics = gets stStatistics
