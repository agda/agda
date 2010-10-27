
-- | Wrappers for 'IORef's.
module Agda.Utils.Pointer where

import Control.Monad.Trans
import Data.IORef

type Ptr a = IORef a

deref :: MonadIO io => Ptr a -> io a
deref p = liftIO $ readIORef p

store :: MonadIO io => Ptr a -> a -> io ()
store p x = liftIO $ writeIORef p x

alloc :: MonadIO io => a -> io (Ptr a)
alloc x = liftIO $ newIORef x

updatePtr :: MonadIO io => Ptr a -> (a -> io a) -> io a
updatePtr p f = do
    x <- deref p
    y <- f x
    store p y
    return y
