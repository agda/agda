{-# OPTIONS -fglasgow-exts #-}

module Utils.Monad.Undo where

import Control.Monad.Trans
import Control.Monad.State
import Control.Monad.Reader
import Control.Monad.Error

-- | An undo monad is a state monad with backtracking.
class MonadState s m => MonadUndo s m where
    undo    :: m ()
    setUndo :: m ()

-- | The undo monad transformer turns any state monad into an undo monad.
newtype UndoT s m a = UndoT { unUndoT :: StateT [s] m a }
    deriving (Monad, MonadTrans, MonadIO)

instance (MonadState s m, Monad m) => MonadUndo s (UndoT s m) where
    undo =
	do  xs <- UndoT get
	    case xs of
		[]   -> return ()
		x:xs ->
		    do	UndoT $ put xs
			lift $ put x
    setUndo =
	do  x <- lift get
	    UndoT $ modify (x:)

instance MonadState s m => MonadState s (UndoT s' m) where
    get = lift get
    put = lift . put

instance MonadReader e m => MonadReader e (UndoT s m) where
    ask	      = lift ask
    local f m = UndoT $ local f $ unUndoT m

instance MonadError e m => MonadError e (UndoT s m) where
    throwError	   = lift . throwError
    catchError m h = UndoT $ catchError (unUndoT m) (unUndoT . h)

