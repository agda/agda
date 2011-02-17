
module Agda.TypeChecking.Monad.Statistics
    ( tick
    , getStatistics
    ) where

import Control.Monad.State
import Data.Map as Map

import Agda.TypeChecking.Monad.Base

tick :: String -> TCM ()
tick x = modify $ \s ->
  let st' = inc $ stStatistics s in
  force st' `seq` s { stStatistics = st' }
  where
    -- We need to be strict in the map
    force m = sum (Map.elems m)
    inc = Map.insertWith (\_ n -> n + 1) x 1

getStatistics :: TCM Statistics
getStatistics = gets stStatistics
