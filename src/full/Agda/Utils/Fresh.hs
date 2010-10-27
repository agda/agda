{-# LANGUAGE MultiParamTypeClasses #-}

{-| A common interface for monads which allow some kind of fresh name
    generation.
-}
module Agda.Utils.Fresh where

import Control.Monad.State
import Control.Monad.Reader

class HasFresh i a where
    nextFresh :: a -> (i,a)

fresh :: (HasFresh i s, MonadState s m) => m i
fresh =
    do	(i,s) <- gets nextFresh
	put s
	return i

withFresh :: (HasFresh i e, MonadReader e m) => (i -> m a) -> m a
withFresh ret =
    do	(i,e) <- asks nextFresh
	local (const e) $ ret i
