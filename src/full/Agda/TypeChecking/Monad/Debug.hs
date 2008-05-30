
module Agda.TypeChecking.Monad.Debug where

import Prelude hiding ( putStrLn )
import Agda.Utils.IO	      ( putStrLn )

import Control.Monad.Trans ( MonadIO(liftIO) )

debug :: MonadIO m => String -> m ()
debug s = liftIO $ putStrLn s

