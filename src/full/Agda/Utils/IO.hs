{-# OPTIONS_GHC -Wunused-imports #-}

-- | Auxiliary functions for the IO monad.

module Agda.Utils.IO where

import Control.Exception
import Control.Monad.State
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

-- | Upon exception, the state is reset.
--
instance CatchIO m => CatchIO (StateT s m) where
  catchIO m h = StateT $ \s -> runStateT m s `catchIO` \ e -> runStateT (h e) s
