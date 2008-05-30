{-# OPTIONS -fglasgow-exts -fallow-undecidable-instances #-}

module Agda.Utils.Monad.Undo where

import Control.Monad.Trans
import Control.Monad.State
import Control.Monad.Reader
import Control.Monad.Error

import Agda.Utils.Monad

-- | An undo monad is a state monad with backtracking.
class (Functor m, MonadState s m) => MonadUndo s m | m -> s where
    undo    :: m ()
    setUndo :: m ()
    getUndoStack :: m [s]
    putUndoStack :: [s] -> m ()

-- | The undo monad transformer turns any state monad into an undo monad.
newtype UndoT s m a = UndoT { unUndoT :: StateT [s] m a }
    deriving (Functor, Monad, MonadTrans, MonadIO)

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

    getUndoStack    = UndoT $ get
    putUndoStack ss = UndoT $ put ss

instance MonadState s m => MonadState s (UndoT s' m) where
    get = lift get
    put = lift . put

instance MonadReader e m => MonadReader e (UndoT s m) where
    ask	      = lift ask
    local f m = UndoT $ local f $ unUndoT m

instance MonadError e m => MonadError e (UndoT s m) where
    throwError	   = lift . throwError
    catchError m h = UndoT $ catchError (unUndoT m) (unUndoT . h)

runUndoT :: Monad m => UndoT s m a -> m a
runUndoT (UndoT sm) = evalStateT sm []

getUndoStateNumber :: MonadUndo s m => m Int
getUndoStateNumber = length <$> getUndoStack

clearUndoHistory :: MonadUndo s m => m ()
clearUndoHistory = putUndoStack []

