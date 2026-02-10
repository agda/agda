-- | Wrappers around 'MVar's which provides an atomic modification operation.
module Agda.Utils.Atomic
  ( Atomic
  , newAtomic
  , readAtomic
  , modifyAtomic
  , withAtomic
  )
  where

import Control.Monad.IO.Class
import Control.Monad.Catch
import Control.DeepSeq

import Control.Concurrent
import Control.Exception (evaluate)

-- | A mutable variable which can be read from and *modified*.
-- This provides a 'modifyAtomic' combinator with atomic semantics for
-- modification, unlike 'modifyMVar'.
newtype Atomic a = Atomic { unAtomic :: MVar a }
  deriving (Eq, NFData)

-- Implementation note: the caveat to modifyMVar's atomicity is that it
-- is possible for another thread to have a *different* value of 'a',
-- which they can 'putMVar', while the continuation to 'modifyMVar' is
-- executing (since the variable is left in the empty state for its
-- duration). This would block the call to 'modifyMVar' after the end of
-- the continuation.
--
-- By contrast, we simply do not export a "put" variant of writing to an
-- atomic. This should, hopefully, be enough to ensure atomicity.

-- | Create a new atomic variable with the given initial value.
newAtomic :: MonadIO m => a -> m (Atomic a)
newAtomic = liftIO . fmap Atomic . newMVar

-- | Read the current state of the atomic variable, waiting if any other
-- thread is modifying it.
--
-- Like 'readMVar', 'readAtomic' is multiple-wakeup, which means that
-- all threads waiting on a modification will be woken up when it
-- finishes.
readAtomic :: MonadIO m => Atomic a -> m a
readAtomic = liftIO . readMVar . unAtomic
{-# INLINE readAtomic #-}

-- | Modify the contents of an atomic variable. If the continuation
-- fails, or receives an asynchronous exception, the variable is
-- returned to its old state.
--
-- No thread, *including the calling thread*, can access the contents of
-- the same 'Atomic' while this function is executing, for reading *or*
-- writing. This means that *any* nested use of the variable, as in
--
-- @
-- f var = modifyAtomic var \old ->
--   -- ...
--   modifyAtomic var \old' -> ... -- (!)
--   readAtomic var                -- (!)
-- @
--
-- will result in a deadlock. The new state of the variable is evaluated
-- (to WHNF).
modifyAtomic :: (MonadIO m, MonadMask m) => Atomic a -> (a -> m (a, b)) -> m b
modifyAtomic (Atomic var) k = mask \restore -> do
  old <- liftIO $ takeMVar var
  (new, ret) <- restore (k old >>= liftIO . evaluate)
    `onException` liftIO (putMVar var old)
  ret <$ liftIO (putMVar var $! new)

{-# SPECIALISE modifyAtomic :: Atomic a -> (a -> IO (a, b)) -> IO b #-}

withAtomic :: (MonadIO m, MonadMask m) => Atomic a -> (a -> m ()) -> m ()
withAtomic var k = modifyAtomic var \val -> (val,) <$> k val
