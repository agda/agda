
module TypeChecking.Monad.Debug where

import Prelude hiding ( putStrLn )
import Utils.IO	      ( putStrLn )

import Control.Monad.Trans ( liftIO )

import TypeChecking.Monad.Base

debug :: String -> TCM ()
debug s = liftIO $ putStrLn s

