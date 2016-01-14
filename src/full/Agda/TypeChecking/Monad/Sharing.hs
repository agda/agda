{-# LANGUAGE CPP              #-}
{-# LANGUAGE FlexibleContexts #-}

module Agda.TypeChecking.Monad.Sharing where

import Control.Applicative
import Control.Monad.Reader
import Data.List
import Data.Function
import Data.Traversable

import Agda.Syntax.Internal
import Agda.TypeChecking.Monad.Base
import Agda.TypeChecking.Monad.Options
import Agda.Utils.Monad

#include "undefined.h"
import Agda.Utils.Impossible

updateSharedTerm :: MonadReader TCEnv m => (Term -> m Term) -> Term -> m Term
updateSharedTerm f v =
  ifM (asks envAllowDestructiveUpdate)
      (updateSharedM f v)
      (f $ ignoreSharing v)

updateSharedTermF
#if __GLASGOW_HASKELL__ <= 708
  :: (Applicative m, MonadReader TCEnv m, Traversable f)
#else
  :: (MonadReader TCEnv m, Traversable f)
#endif
  => (Term -> m (f Term)) -> Term -> m (f Term)
updateSharedTermF f v =
  ifM (asks envAllowDestructiveUpdate)
      (updateSharedFM f v)
      (f $ ignoreSharing v)

updateSharedTermT :: (MonadTCM tcm, MonadTrans t, Monad (t tcm)) => (Term -> t tcm Term) -> Term -> t tcm Term
updateSharedTermT f v =
  ifM (lift $ asks envAllowDestructiveUpdate)
      (updateSharedM f v)
      (f $ ignoreSharing v)

forceEqualTerms :: Term -> Term -> TCM ()
forceEqualTerms u v =
  whenM (asks envAllowDestructiveUpdate) $
  when (null $ (intersect `on` pointerChain) u v) $
  case (u, v) of
    (Shared p, Shared q) | p > q -> update u v
    (_, Shared{})                -> update v u
    (Shared{}, _)                -> update u v
    _ -> return ()
  where
    -- TODO: compress pointer chain
    update u@(Shared{}) v = do
        report u v
        setPtr v p `seq` compressPointerChain u `seq` return ()
      where p = last $ pointerChain u
    update _ _ = __IMPOSSIBLE__
    report x y = reportSLn "tc.ptr" 50 $ "setting " ++ show x ++ "\n     to " ++ show y

