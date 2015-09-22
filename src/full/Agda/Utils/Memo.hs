{-# LANGUAGE CPP        #-}
{-# LANGUAGE RankNTypes #-}

module Agda.Utils.Memo where

#if __GLASGOW_HASKELL__ <= 708
import Control.Applicative ( (<$) )
#endif

import Control.Monad.State
import Agda.Utils.Lens

-- Simple memoisation in a state monad

#if __GLASGOW_HASKELL__ <= 708
memo :: (Functor m, MonadState s m) => Lens' (Maybe a) s -> m a -> m a
#else
memo :: MonadState s m => Lens' (Maybe a) s -> m a -> m a
#endif
memo tbl compute = do
  mv <- use tbl
  case mv of
    Just x  -> return x
    Nothing -> do
      x <- compute
      x <$ (tbl .= Just x)

