
module Agda.Mimer.Monad where

import Control.Monad.IO.Class (liftIO)
import Control.Monad.Reader (ReaderT, asks)
import Data.IORef (modifyIORef')

import Agda.TypeChecking.Monad (TCM, verboseS)
import Agda.Mimer.Types

type SM a = ReaderT SearchOptions TCM a

updateStat :: (MimerStats -> MimerStats) -> SM ()
updateStat f = verboseS "mimer.stats" 10 $ do
  ref <- asks searchStats
  liftIO $ modifyIORef' ref f

