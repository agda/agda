
module Agda.TypeChecking.Monad.Debug where

import qualified System.IO.UTF8 as UTF8
import Control.Monad.Trans ( MonadIO(liftIO) )

debug :: MonadIO m => String -> m ()
debug s = liftIO $ UTF8.putStrLn s