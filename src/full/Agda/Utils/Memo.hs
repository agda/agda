{-# LANGUAGE RankNTypes #-}
module Agda.Utils.Memo where

import Control.Monad.State
import Agda.Utils.Lens

-- Simple memoisation in a state monad

memo :: MonadState s m => Lens' (Maybe a) s -> m a -> m a
memo tbl compute = do
  mv <- use tbl
  case mv of
    Just x  -> return x
    Nothing -> do
      x <- compute
      x <$ (tbl .= Just x)

