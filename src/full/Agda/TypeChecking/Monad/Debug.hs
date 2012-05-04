
module Agda.TypeChecking.Monad.Debug where

import Control.Monad.Trans ( MonadIO(liftIO) )

debug :: MonadIO m => String -> m ()
debug s = liftIO $ putStrLn s
