{-# LANGUAGE CPP #-}
module Agda.TypeChecking.Monad.Sharing where

import Control.Monad.Reader
import Data.List
import Data.Function
import Data.Traversable

import Agda.Syntax.Internal
import Agda.TypeChecking.Monad.Base
import Agda.TypeChecking.Monad.Options
import Agda.Utils.Monad
import Agda.Utils.Impossible

#include "../../undefined.h"

updateSharedTerm :: MonadTCM tcm => (Term -> tcm Term) -> Term -> tcm Term
updateSharedTerm f v =
  ifM (liftTCM $ asks envAllowDestructiveUpdate)
      (updateSharedM f v)
      (f $ ignoreSharing v)

updateSharedTermF :: (MonadTCM tcm, Traversable f) => (Term -> tcm (f Term)) -> Term -> tcm (f Term)
updateSharedTermF f v =
  ifM (liftTCM $ asks envAllowDestructiveUpdate)
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

disableDestructiveUpdate :: TCM a -> TCM a
disableDestructiveUpdate = local $ \e -> e { envAllowDestructiveUpdate = False }

