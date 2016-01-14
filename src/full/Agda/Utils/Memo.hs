{-# LANGUAGE CPP        #-}
{-# LANGUAGE RankNTypes #-}

module Agda.Utils.Memo where

import Control.Applicative
import Control.Monad.State
import Agda.Utils.Lens

-- Simple memoisation in a state monad

-- | Simple, non-reentrant memoisation.
memo
#if __GLASGOW_HASKELL__ <= 708
  :: (Functor m, MonadState s m)
#else
  :: MonadState s m
#endif
  => Lens' (Maybe a) s -> m a -> m a
memo tbl compute = do
  mv <- use tbl
  case mv of
    Just x  -> return x
    Nothing -> do
      x <- compute
      x <$ (tbl .= Just x)

-- | Recursive memoisation, second argument is the value you get
--   on recursive calls.
memoRec
#if __GLASGOW_HASKELL__ <= 708
  :: (Functor m, MonadState s m)
#else
  :: MonadState s m
#endif
  => Lens' (Maybe a) s -> a -> m a -> m a
memoRec tbl ih compute = do
  mv <- use tbl
  case mv of
    Just x  -> return x
    Nothing -> do
      tbl .= Just ih
      x <- compute
      x <$ (tbl .= Just x)
