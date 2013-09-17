
module Debug where

import Debug.Trace

debug :: Monad m => String -> m ()
debug s = trace s $ return ()

