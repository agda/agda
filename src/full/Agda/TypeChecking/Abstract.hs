{-# LANGUAGE CPP, FlexibleInstances #-}

-- | Functions for abstracting terms over other terms.
module Agda.TypeChecking.Abstract where

import Agda.Syntax.Common hiding (Arg, Dom, NamedArg)
import qualified Agda.Syntax.Common as Common
import Agda.Syntax.Internal
import Agda.TypeChecking.Substitute
import Data.Function

#include "../undefined.h"
import Agda.Utils.Impossible

piAbstractTerm :: Term -> Type -> Type -> Type
piAbstractTerm v a b = fun a (abstractTerm v b)
  where
    fun a b = El s $ Pi (Common.Dom defaultArgInfo a) $ mkAbs "w" b
      where s = (sLub `on` getSort) a b

class AbstractTerm a where
  -- | @subst u . abstractTerm u == id@
  abstractTerm :: Term -> a -> a

instance AbstractTerm Term where
  abstractTerm u v = case v of
    v | u == v  -> Var 0 []
    Var i vs    -> Var (i + 1) $ absT vs
    Lam h b     -> Lam h $ absT b
    Def c vs    -> Def c $ absT vs
    Con c vs    -> Con c $ absT vs
    Pi a b      -> uncurry Pi $ absT (a, b)
    Lit l       -> Lit l
    Level l     -> Level $ absT l
    Sort s      -> Sort $ absT s
    MetaV m vs  -> MetaV m $ absT vs
    DontCare mv -> DontCare $ absT mv
    Shared p    -> Shared $ absT p
    where
      absT x = abstractTerm u x

instance AbstractTerm a => AbstractTerm (Ptr a) where
  abstractTerm u = fmap (abstractTerm u)

instance AbstractTerm Type where
  abstractTerm u (El s v) = El (abstractTerm u s) (abstractTerm u v)

instance AbstractTerm Sort where
  abstractTerm u s = case s of
    Type n     -> Type $ absS n
    Prop       -> Prop
    Inf        -> Inf
    DLub s1 s2 -> DLub (absS s1) (absS s2)
    where absS x = abstractTerm u x

instance AbstractTerm Level where
  abstractTerm u (Max as) = Max $ abstractTerm u as

instance AbstractTerm PlusLevel where
  abstractTerm u l@ClosedLevel{} = l
  abstractTerm u (Plus n l) = Plus n $ abstractTerm u l

instance AbstractTerm LevelAtom where
  abstractTerm u l = case l of
    MetaLevel m vs   -> MetaLevel m    $ abstractTerm u vs
    NeutralLevel v   -> NeutralLevel   $ abstractTerm u v
    BlockedLevel _ v -> UnreducedLevel $ abstractTerm u v -- abstracting might remove the blockage
    UnreducedLevel v -> UnreducedLevel $ abstractTerm u v

instance AbstractTerm a => AbstractTerm (Arg a) where
  abstractTerm = fmap . abstractTerm

instance AbstractTerm a => AbstractTerm (Dom a) where
  abstractTerm = fmap . abstractTerm

instance AbstractTerm a => AbstractTerm [a] where
  abstractTerm = fmap . abstractTerm

instance AbstractTerm a => AbstractTerm (Maybe a) where
  abstractTerm = fmap . abstractTerm

instance (Subst a, AbstractTerm a) => AbstractTerm (Abs a) where
  abstractTerm u (NoAbs x v) = NoAbs x $ abstractTerm u v
  abstractTerm u (Abs   x v) = Abs x $ applySubst swap $ abstractTerm (raise 1 u) v
    where
      -- This swaps var 0 and var 1 (we hope)
      swap = var 1 :# liftS 1 (raiseS 1)

instance (AbstractTerm a, AbstractTerm b) => AbstractTerm (a, b) where
  abstractTerm u (x, y) = (abstractTerm u x, abstractTerm u y)
