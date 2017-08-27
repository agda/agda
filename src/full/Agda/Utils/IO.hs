-- | Auxiliary functions for the IO monad.

module Agda.Utils.IO where

import Control.Exception
import Control.Monad.Writer

-- | Catch 'IOException's.
--
class CatchIO m where
  catchIO :: m a -> (IOException -> m a) -> m a

-- | Alias of 'catch' for the IO monad.
--
instance CatchIO IO where
  catchIO = catch

-- | Upon exception, the written output is lost.
--
instance CatchIO m => CatchIO (WriterT w m) where
  catchIO m h = WriterT $ runWriterT m `catchIO` \ e -> runWriterT (h e)
