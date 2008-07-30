{-# OPTIONS -cpp #-}

-- | Functions for abstracting terms over other terms.
module Agda.TypeChecking.Abstract where

import Agda.Syntax.Common
import Agda.Syntax.Internal
import Agda.TypeChecking.Substitute
import Data.Function

#include "../undefined.h"
import Agda.Utils.Impossible

piAbstractTerm :: Term -> Type -> Type -> Type
piAbstractTerm v a b = fun a (abstractTerm v b)
  where
    fun a b = El s $ Pi (Arg NotHidden a) $ Abs "w" b
      where s = (sLub `on` getSort) a b

class AbstractTerm a where
  -- | @subst u . abstractTerm u == id@
  abstractTerm :: Term -> a -> a

instance AbstractTerm Term where
  abstractTerm u v = case ignoreBlocking v of
    v | u == v  -> Var 0 []
    Var i vs    -> Var (i + 1) $ absT vs
    Lam h b     -> Lam h $ absT b
    Def c vs    -> Def c $ absT vs
    Con c vs    -> Con c $ absT vs
    Pi a b      -> uncurry Pi $ absT (a, b)
    Fun a b      -> uncurry Fun $ absT (a, b)
    Lit l       -> Lit l
    Sort s      -> Sort s
    MetaV m vs  -> MetaV m $ absT vs
    BlockedV _  -> __IMPOSSIBLE__
    where
      absT x = abstractTerm u x

instance AbstractTerm Type where
  abstractTerm u (El s v) = El s $ abstractTerm u v

instance AbstractTerm a => AbstractTerm (Arg a) where
  abstractTerm = fmap . abstractTerm

instance AbstractTerm a => AbstractTerm [a] where
  abstractTerm = fmap . abstractTerm

instance (Subst a, AbstractTerm a) => AbstractTerm (Abs a) where
  abstractTerm u (Abs x v) = Abs x $ swap $ abstractTerm (raise 1 u) v
    where
      swap = substs $ [Var 1 [], Var 0 []] ++ [Var i [] | i <- [2..]]

instance (AbstractTerm a, AbstractTerm b) => AbstractTerm (a, b) where
  abstractTerm u (x, y) = (abstractTerm u x, abstractTerm u y)

