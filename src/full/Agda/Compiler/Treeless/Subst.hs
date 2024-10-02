{-# OPTIONS_GHC -fno-warn-orphans       #-}

module Agda.Compiler.Treeless.Subst where

import qualified Data.IntMap as IntMap
import Data.IntMap (IntMap)
import Data.Maybe
import Data.Semigroup ( Semigroup, (<>), All(..), Any(..) )

import Agda.Syntax.Treeless
import Agda.TypeChecking.Substitute

import Agda.Utils.Impossible

instance DeBruijn TTerm where
  deBruijnVar = TVar
  deBruijnView (TVar i) = Just i
  deBruijnView _ = Nothing

instance Subst TTerm where
  type SubstArg TTerm = TTerm

  applySubst IdS = id
  applySubst rho = \case
      t@TDef{}    -> t
      t@TLit{}    -> t
      t@TCon{}    -> t
      t@TPrim{}   -> t
      t@TUnit{}   -> t
      t@TSort{}   -> t
      t@TErased{} -> t
      t@TError{}  -> t
      TVar i         -> lookupS rho i
      TApp f ts      -> tApp (applySubst rho f) (applySubst rho ts)
      TLam b         -> TLam (applySubst (liftS 1 rho) b)
      TLet e b       -> TLet (applySubst rho e) (applySubst (liftS 1 rho) b)
      TCase i t d bs ->
        case applySubst rho (TVar i) of
          TVar j  -> TCase j t (applySubst rho d) (applySubst rho bs)
          e       -> TLet e $ TCase 0 t (applySubst rho' d) (applySubst rho' bs)
            where rho' = wkS 1 rho
      TCoerce e -> TCoerce (applySubst rho e)
    where
      tApp (TPrim PSeq) [TErased, b] = b
      tApp f ts = TApp f ts

instance Subst TAlt where
  type SubstArg TAlt = TTerm
  applySubst rho (TACon c i b) = TACon c i (applySubst (liftS i rho) b)
  applySubst rho (TALit l b)   = TALit l (applySubst rho b)
  applySubst rho (TAGuard g b) = TAGuard (applySubst rho g) (applySubst rho b)

newtype UnderLambda = UnderLambda Any
  deriving (Eq, Ord, Show, Semigroup, Monoid)

newtype SeqArg = SeqArg All
  deriving (Eq, Ord, Show, Semigroup, Monoid)

data Occurs = Occurs Int UnderLambda SeqArg
  deriving (Eq, Ord, Show)

once :: Occurs
once = Occurs 1 mempty (SeqArg $ All False)

inSeq :: Occurs -> Occurs
inSeq (Occurs n l _) = Occurs n l mempty

underLambda :: Occurs -> Occurs
underLambda o = o <> Occurs 0 (UnderLambda $ Any True) mempty

instance Semigroup Occurs where
  Occurs a k s <> Occurs b l t = Occurs (a + b) (k <> l) (s <> t)

instance Monoid Occurs where
  mempty  = Occurs 0 mempty mempty
  mappend = (<>)


-- Andreas, 2019-07-10: this free variable computation should be rewritten
-- in the style of TypeChecking.Free.Lazy.
-- https://github.com/agda/agda/commit/03eb3945114a4ccdb449f22d69db8d6eaa4699b8#commitcomment-34249120

class HasFree a where
  freeVars :: a -> IntMap Occurs

freeIn :: HasFree a => Int -> a -> Bool
freeIn i x = IntMap.member i (freeVars x)

occursIn :: HasFree a => Int -> a -> Occurs
occursIn i x = fromMaybe mempty $ IntMap.lookup i (freeVars x)

instance HasFree Int where
  freeVars x = IntMap.singleton x once

instance HasFree a => HasFree [a] where
  freeVars xs = IntMap.unionsWith mappend $ map freeVars xs

instance (HasFree a, HasFree b) => HasFree (a, b) where
  freeVars (x, y) = IntMap.unionWith mappend (freeVars x) (freeVars y)

data Binder a = Binder Int a

instance HasFree a => HasFree (Binder a) where
  freeVars (Binder 0 x) = freeVars x
  freeVars (Binder k x) = IntMap.filterWithKey (\ k _ -> k >= 0) $ IntMap.mapKeysMonotonic (subtract k) $ freeVars x

newtype InSeq a = InSeq a

instance HasFree a => HasFree (InSeq a) where
  freeVars (InSeq x) = inSeq <$> freeVars x

instance HasFree TTerm where
  freeVars = \case
    TDef{}    -> IntMap.empty
    TLit{}    -> IntMap.empty
    TCon{}    -> IntMap.empty
    TPrim{}   -> IntMap.empty
    TUnit{}   -> IntMap.empty
    TSort{}   -> IntMap.empty
    TErased{} -> IntMap.empty
    TError{}  -> IntMap.empty
    TVar i         -> freeVars i
    TApp (TPrim PSeq) [TVar x, b] -> freeVars (InSeq x, b)
    TApp f ts      -> freeVars (f, ts)
    TLam b         -> underLambda <$> freeVars (Binder 1 b)
    TLet e b       -> freeVars (e, Binder 1 b)
    TCase i _ d bs -> freeVars (i, (d, bs))
    TCoerce t      -> freeVars t

instance HasFree TAlt where
  freeVars = \case
    TACon _ i b -> freeVars (Binder i b)
    TALit _ b   -> freeVars b
    TAGuard g b -> freeVars (g, b)

-- | Strenghtening.
tryStrengthen :: (HasFree a, Subst a) => Int -> a -> Maybe a
tryStrengthen n t =
  case IntMap.minViewWithKey (freeVars t) of
    Just ((i, _), _) | i < n -> Nothing
    _ -> Just $ applySubst (strengthenS impossible n) t
