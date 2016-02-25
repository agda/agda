{-# LANGUAGE CPP #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE UndecidableInstances #-}

-- | Functions for abstracting terms over other terms.
module Agda.TypeChecking.Abstract where

import Control.Applicative
import Control.Monad
import Control.Monad.State
import Data.Function
import Data.Traversable

import Agda.Syntax.Common
import Agda.Syntax.Internal

import Agda.TypeChecking.Monad
import Agda.TypeChecking.Monad.Builtin (equalityUnview)
import Agda.TypeChecking.Substitute
import Agda.TypeChecking.CheckInternal
import Agda.TypeChecking.Conversion
import Agda.TypeChecking.Constraints
import Agda.TypeChecking.Pretty

import Agda.Utils.Functor
import Agda.Utils.List (splitExactlyAt)
import Agda.Utils.Size
import Agda.Utils.Except
import qualified Agda.Utils.HashMap as HMap

import Agda.Utils.Impossible
#include "undefined.h"

typeOf :: Type -> Type
typeOf = sort . getSort

-- Doesn't abstract in the sort.
abstractType :: Type -> Term -> Type -> TCM Type
abstractType a v (El s b) = El (raise 1 s) <$> abstractTerm a v (sort s) b

-- | @piAbstractTerm v a b[v] = (w : a) -> b[w]@
piAbstractTerm :: Term -> Type -> Type -> TCM Type
piAbstractTerm v a b = do
  fun <- mkPi (defaultDom ("w", a)) <$> abstractType a v b
  reportSDoc "tc.abstract" 50 $
    sep [ text "piAbstract" <+> sep [ prettyTCM v <+> text ":", nest 2 $ prettyTCM a ]
        , nest 2 $ text "from" <+> prettyTCM b
        , nest 2 $ text "-->" <+> prettyTCM fun ]
  return fun

-- | @piAbstract (v, a) b[v] = (w : a) -> b[w]@
--
--   For @rewrite@, it does something special:
--
--   @piAbstract (prf, Eq a v v') b[v,prf] = (w : a) (w' : Eq a w v') -> b[w,w']@

piAbstract :: (Term, EqualityView) -> Type -> TCM Type
piAbstract (v, OtherType a) b = piAbstractTerm v a b
piAbstract (prf, eqt@(EqualityType s _ _ a v _)) b = do
  let prfTy = equalityUnview eqt
      vTy   = El s (unArg a)
  b <- abstractType prfTy prf b
  b <- addContext ("w", defaultDom prfTy) $ abstractType (raise 1 vTy) (unArg $ raise 1 v) b
  return . funType vTy . funType eqTy' . swap01 $ b
  where
    funType a = mkPi $ defaultDom ("w", a)
    -- Abstract the lhs (@a@) of the equality only.
    eqt1  = raise 1 eqt
    eqTy' = equalityUnview $ eqt1 { eqtLhs = eqtLhs eqt1 $> var 0 }

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

-- Type-based abstraction. Needed if u is a constructor application (#745).
abstractTerm :: Type -> Term -> Type -> Term -> TCM Term
abstractTerm a u@Con{} b v = do
  reportSDoc "tc.abstract" 50 $
    sep [ text "Abstracting"
        , nest 2 $ sep [ prettyTCM u <+> text ":", nest 2 $ prettyTCM a ]
        , text "over"
        , nest 2 $ sep [ prettyTCM v <+> text ":", nest 2 $ prettyTCM b ] ]

  hole <- qualify <$> currentModule <*> freshName_ "hole"
  noMutualBlock $ addConstant hole $ defaultDefn defaultArgInfo hole a Axiom

  args <- map Apply <$> getContextArgs
  let n = length args

  let abstr b v = do
        m <- size <$> getContext
        let (a', u') = raise (m - n) (a, u)
        case isPrefixOf u' v of
          Nothing -> return v
          Just es -> do -- Check that the types match.
            s <- get
            do  disableDestructiveUpdate (noConstraints $ equalType a' b)
                put s
                return $ Def hole (raise (m - n) args ++ es)
              `catchError` \ _ -> do
                reportSDoc "tc.abstract.ill-typed" 50 $
                  sep [ text "Skipping ill-typed abstraction"
                      , nest 2 $ sep [ prettyTCM v <+> text ":", nest 2 $ prettyTCM b ] ]
                return v

  v <- catchError_ (checkInternal' (defaultAction { preAction = abstr }) v b) $ \ err -> do
        reportSDoc "impossible" 10 $
          vcat [ text "Type error in term to abstract"
               , nest 2 $ (prettyTCM =<< getContextTelescope) <+> text "⊢"
               , nest 2 $ sep [ prettyTCM v <+> text ":", nest 2 $ prettyTCM b ]
               , nest 2 $ prettyTCM err ]
        __IMPOSSIBLE__
  reportSDoc "tc.abstract" 50 $ sep [ text "Resulting abstraction", nest 2 $ prettyTCM v ]
  modifySignature $ updateDefinitions $ HMap.delete hole
  return $ absTerm (Def hole args) v

abstractTerm _ u _ v = return $ absTerm u v -- Non-constructors can use untyped abstraction

class AbsTerm a where
  -- | @subst u . absTerm u == id@
  absTerm :: Term -> a -> a

instance AbsTerm Term where
  absTerm u v | Just es <- u `isPrefixOf` v = Var 0 $ absT es
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
        absT x = absTerm u x

instance AbsTerm a => AbsTerm (Ptr a) where
  absTerm u = fmap (absTerm u)

instance AbsTerm Type where
  absTerm u (El s v) = El (absTerm u s) (absTerm u v)

instance AbsTerm Sort where
  absTerm u s = case s of
    Type n     -> Type $ absS n
    Prop       -> Prop
    Inf        -> Inf
    SizeUniv   -> SizeUniv
    DLub s1 s2 -> DLub (absS s1) (absS s2)
    where absS x = absTerm u x

instance AbsTerm Level where
  absTerm u (Max as) = Max $ absTerm u as

instance AbsTerm PlusLevel where
  absTerm u l@ClosedLevel{} = l
  absTerm u (Plus n l) = Plus n $ absTerm u l

instance AbsTerm LevelAtom where
  absTerm u l = case l of
    MetaLevel m vs   -> MetaLevel m    $ absTerm u vs
    NeutralLevel r v -> NeutralLevel r $ absTerm u v
    BlockedLevel _ v -> UnreducedLevel $ absTerm u v -- abstracting might remove the blockage
    UnreducedLevel v -> UnreducedLevel $ absTerm u v

instance AbsTerm a => AbsTerm (Elim' a) where
  absTerm = fmap . absTerm

instance AbsTerm a => AbsTerm (Arg a) where
  absTerm = fmap . absTerm

instance AbsTerm a => AbsTerm (Dom a) where
  absTerm = fmap . absTerm

instance AbsTerm a => AbsTerm [a] where
  absTerm = fmap . absTerm

instance AbsTerm a => AbsTerm (Maybe a) where
  absTerm = fmap . absTerm

instance (Subst Term a, AbsTerm a) => AbsTerm (Abs a) where
  absTerm u (NoAbs x v) = NoAbs x $ absTerm u v
  absTerm u (Abs   x v) = Abs x $ swap01 $ absTerm (raise 1 u) v

instance (AbsTerm a, AbsTerm b) => AbsTerm (a, b) where
  absTerm u (x, y) = (absTerm u x, absTerm u y)

-- | This swaps @var 0@ and @var 1@.
swap01 :: (Subst Term a) => a -> a
swap01 = applySubst $ var 1 :# liftS 1 (raiseS 1)
