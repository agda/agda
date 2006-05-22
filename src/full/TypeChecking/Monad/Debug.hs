
module TypeChecking.Monad.Debug where

import qualified Data.Map as Map
import Control.Monad.Trans

import Syntax.Internal
import TypeChecking.Monad

debug :: String -> TCM ()
debug s = liftIO $ putStrLn s

