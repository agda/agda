-- | Auxiliary functions for the IO monad.

module Agda.Utils.IO where

import Control.Exception

-- | Alias of 'catch' for the IO monad.
--
catchIO :: IO a -> (IOException -> IO a) -> IO a
catchIO = catch
