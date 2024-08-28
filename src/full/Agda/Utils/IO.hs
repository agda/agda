{-# LANGUAGE CPP #-}

-- | Auxiliary functions for the IO monad.

module Agda.Utils.IO where

import Control.Exception
import Control.Monad.State
import Control.Monad.Writer

import Agda.Utils.List (dropFrom)
import Agda.Utils.String (rtrim)

-- | Catch 'Exception's in an extension of the 'IO' monad.
--
class CatchIO m where
  catchIO :: Exception e => m a -> (e -> m a) -> m a

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

-- | Print an 'IOException' without the call stack.
--
showIOException :: Exception e => e -> String
showIOException =
  rtrim
#if MIN_VERSION_base(4,20,0)
  -- Andreas, 2024-07-05, issue #7299.
  -- Ugly hack to drop call stack (introduced in GHC 9.10) from IOException.
  -- If you have a better solution, please update this.
  . dropFrom "HasCallStack"
#endif
  . displayException
