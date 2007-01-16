
module TypeChecking.Monad.Debug where

import Prelude hiding ( putStrLn )
import Utils.IO	      ( putStrLn )

import Control.Monad.Trans ( MonadIO(liftIO) )

debug :: MonadIO m => String -> m ()
debug s = liftIO $ putStrLn s

