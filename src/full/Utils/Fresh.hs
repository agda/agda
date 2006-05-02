{-# OPTIONS -fglasgow-exts #-}

{-| A common interface for monads which allow some kind of fresh name
    generation.
-}
module Utils.Fresh where

import Control.Monad.State
import Control.Monad.Reader

import Utils.Monad

class HasFresh i a where
    nextFresh :: a -> (i,a)

fresh :: (HasFresh i s, MonadState s m) => m i
fresh =
    do	(i,s) <- nextFresh <$> get
	put s
	return i

withFresh :: (HasFresh i e, MonadReader e m) => (i -> m a) -> m a
withFresh ret =
    do	(i,e) <- nextFresh <$> ask
	local (const e) $ ret i

