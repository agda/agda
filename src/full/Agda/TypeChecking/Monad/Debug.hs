
module Agda.TypeChecking.Monad.Debug where

import qualified Agda.Utils.IO.Locale as LocIO
import Control.Monad.Trans ( MonadIO(liftIO) )

debug :: MonadIO m => String -> m ()
debug s = liftIO $ LocIO.putStrLn s