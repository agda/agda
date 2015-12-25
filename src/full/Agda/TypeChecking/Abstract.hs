{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE UndecidableInstances #-}

-- | Functions for abstracting terms over other terms.
module Agda.TypeChecking.Abstract where

import Control.Monad
import Data.Function

import Agda.Syntax.Common
import Agda.Syntax.Internal

import Agda.TypeChecking.Monad.Builtin (equalityUnview)
import Agda.TypeChecking.Substitute

import Agda.Utils.Functor
import Agda.Utils.List (splitExactlyAt)

-- | @piAbstractTerm v a b[v] = (w : a) -> b[w]@
piAbstractTerm :: Term -> Type -> Type -> Type
piAbstractTerm v a b = mkPi (defaultDom ("w", a)) $ abstractTerm v b

-- | @piAbstract (v, a) b[v] = (w : a) -> b[w]@
--
--   For @rewrite@, it does something special:
--
--   @piAbstract (prf, Eq a v v') b[v,prf] = (w : a) (w' : Eq a w v') -> b[w,w']@

piAbstract :: (Term, EqualityView) -> Type -> Type
piAbstract (v, OtherType a) b = piAbstractTerm v a b
piAbstract (prf, eqt@(EqualityType s _ _ a v _)) b =
  funType (El s $ unArg a) $ funType eqt' $
    swap01 $ abstractTerm (unArg $ raise 1 v) $ abstractTerm prf b
  where
    funType a = mkPi $ defaultDom ("w", a)
    -- Abstract the lhs (@a@) of the equality only.
    eqt1 = raise 1 eqt
    eqt' = equalityUnview $ eqt1 { eqtLhs = eqtLhs eqt1 $> var 0 }

-- | @isPrefixOf u v = Just es@ if @v == u `applyE` es@.
class IsPrefixOf a where
  isPrefixOf :: a -> a -> Maybe Elims

instance IsPrefixOf Elims where
  isPrefixOf us vs = do
    (vs1, vs2) <- splitExactlyAt (length us) vs
    guard $ us == vs1
    return vs2

instance IsPrefixOf Args where
  isPrefixOf us vs = do
    (vs1, vs2) <- splitExactlyAt (length us) vs
    guard $ us == vs1
    return $ map Apply vs2

instance IsPrefixOf Term where
  isPrefixOf u v =
    case (ignoreSharing u, ignoreSharing v) of
      (Var   i us, Var   j vs) | i == j  -> us `isPrefixOf` vs
      (Def   f us, Def   g vs) | f == g  -> us `isPrefixOf` vs
      (Con   c us, Con   d vs) | c == d  -> us `isPrefixOf` vs
      (MetaV x us, MetaV y vs) | x == y  -> us `isPrefixOf` vs
      (u, v) -> guard (u == v) >> return []

class AbstractTerm a where
  -- | @subst u . abstractTerm u == id@
  abstractTerm :: Term -> a -> a

instance AbstractTerm Term where
  abstractTerm u v | Just es <- u `isPrefixOf` v = Var 0 $ absT es
                   | otherwise                   =
    case v of
-- Andreas, 2013-10-20: the original impl. works only at base types
--    v | u == v  -> Var 0 []  -- incomplete see succeed/WithOfFunctionType
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
    SizeUniv   -> SizeUniv
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
    NeutralLevel r v -> NeutralLevel r $ abstractTerm u v
    BlockedLevel _ v -> UnreducedLevel $ abstractTerm u v -- abstracting might remove the blockage
    UnreducedLevel v -> UnreducedLevel $ abstractTerm u v

instance AbstractTerm a => AbstractTerm (Elim' a) where
  abstractTerm = fmap . abstractTerm

instance AbstractTerm a => AbstractTerm (Arg a) where
  abstractTerm = fmap . abstractTerm

instance AbstractTerm a => AbstractTerm (Dom a) where
  abstractTerm = fmap . abstractTerm

instance AbstractTerm a => AbstractTerm [a] where
  abstractTerm = fmap . abstractTerm

instance AbstractTerm a => AbstractTerm (Maybe a) where
  abstractTerm = fmap . abstractTerm

instance (Subst Term a, AbstractTerm a) => AbstractTerm (Abs a) where
  abstractTerm u (NoAbs x v) = NoAbs x $ abstractTerm u v
  abstractTerm u (Abs   x v) = Abs x $ swap01 $ abstractTerm (raise 1 u) v

instance (AbstractTerm a, AbstractTerm b) => AbstractTerm (a, b) where
  abstractTerm u (x, y) = (abstractTerm u x, abstractTerm u y)

-- | This swaps @var 0@ and @var 1@.
swap01 :: (Subst Term a) => a -> a
swap01 = applySubst $ var 1 :# liftS 1 (raiseS 1)
