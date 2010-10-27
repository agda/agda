
module Agda.TypeChecking.Monad.Statistics
    ( tick
    , getStatistics
    ) where

import Control.Monad.State
import Data.Map as Map

import Agda.TypeChecking.Monad.Base

tick :: String -> TCM ()
tick x = modify $ \s ->
    s { stStatistics = Map.insertWith (\_ n -> n + 1) x 1
		     $ stStatistics s
      }

getStatistics :: TCM Statistics
getStatistics = gets stStatistics
