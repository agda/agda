{-# LANGUAGE CPP #-}

module Agda.TypeChecking.DefinitionalEquality where

import Data.Monoid

import Agda.Syntax.Common
import Agda.Syntax.Internal

import Agda.TypeChecking.Reduce
import Agda.TypeChecking.Reduce.Monad

import Agda.Utils.Except

#include "undefined.h"
import Agda.Utils.Impossible

-- | A type-directed definitional equality check that takes eta into account,
--   and reduces terms when needed. It replaces
--   @
--      (v, v') <- normalise (v, v')
--      v == v'
--   @
--   by a more efficient routine that also checks eta rules and produces the
--   proper blocking tags when it encounters unsolved metas.

type DefEqM = ExceptT Blocked_ (WriterT All ReduceM)

blockedOnMeta :: MetaId -> DefEqM a
blockedOnMeta m = throwError $ Blocked m ()

tellNotEqual :: DefEqM ()
tellNotEqual = lift $ tell $ All False

liftRed :: ReduceM a -> DefEqM a
liftRed = lift . lift

class DefEq a t | t -> a where
  defEq  :: a -> t -> t -> DefEqM (a,t,t)

instance DefEq Type Term where
  defEq a u v = do
    ((u,v), equal) <- liftRed $ checkSyntacticEquality u v
    if equal then return (a,u,v) else do
    (a,u,v) <- liftRed $ reduce' (a,u,v)
    case ignoreSharing (unEl a) of
    -- TODO sizes
    -- TODO levels
        Var i es   -> ???
        Lam _ _    -> __IMPOSSIBLE__
        Lit _      -> __IMPOSSIBLE__
        Def r es   -> do
          isrec <- isEtaRecord r
          if isrec then do
            ???
            else
        Con _ _    -> __IMPOSSIBLE__
        Pi a b     -> ???
        Sort s     -> ???
        Level _    -> __IMPOSSIBLE__
        MetaV m es -> blockedOnMeta m
        DontCare


