{-# LANGUAGE MultiParamTypeClasses #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}

module Agda.Compiler.Treeless.Subst where

import qualified Data.Set as Set
import Data.Set (Set)

import Agda.Syntax.Treeless
import Agda.Syntax.Internal (Substitution'(..))
import Agda.TypeChecking.Substitute

instance DeBruijn TTerm where
  debruijnVar = TVar
  debruijnView (TVar i) = Just i
  debruijnView _ = Nothing

instance Subst TTerm TTerm where
  applySubst IdS t = t
  applySubst rho t = case t of
    TDef{}    -> t
    TLit{}    -> t
    TCon{}    -> t
    TPrim{}   -> t
    TUnit{}   -> t
    TSort{}   -> t
    TErased{} -> t
    TError{}  -> t
    TVar i         -> lookupS rho i
    TApp f ts      -> TApp (applySubst rho f) (applySubst rho ts)
    TLam b         -> TLam (applySubst (liftS 1 rho) b)
    TLet e b       -> TLet (applySubst rho e) (applySubst (liftS 1 rho) b)
    TCase i t d bs ->
      case applySubst rho (TVar i) of
        TVar j -> TCase j t (applySubst rho d) (applySubst rho bs)
        e -> TLet e $ TCase 0 t (applySubst rho' d) (applySubst rho' bs)
          where rho' = wkS 1 rho

instance Subst TTerm TAlt where
  applySubst rho (TACon c i b)  = TACon c i (applySubst (liftS i rho) b)
  applySubst rho (TALit l b)  = TALit l (applySubst rho b)
  applySubst rho (TAGuard g b) = TAGuard (applySubst rho g) (applySubst rho b)

class HasFree a where
  freeVars :: a -> Set Int

freeIn :: HasFree a => Int -> a -> Bool
freeIn i x = Set.member i (freeVars x)

instance HasFree Int where
  freeVars = Set.singleton

instance HasFree a => HasFree [a] where
  freeVars xs = Set.unions $ map freeVars xs

instance (HasFree a, HasFree b) => HasFree (a, b) where
  freeVars (x, y) = Set.union (freeVars x) (freeVars y)

data Binder a = Binder Int a

instance HasFree a => HasFree (Binder a) where
  freeVars (Binder 0 x) = freeVars x
  freeVars (Binder k x) = Set.filter (>= 0) $ Set.mapMonotonic (subtract k) $ freeVars x

instance HasFree TTerm where
  freeVars t = case t of
    TDef{}    -> Set.empty
    TLit{}    -> Set.empty
    TCon{}    -> Set.empty
    TPrim{}   -> Set.empty
    TUnit{}   -> Set.empty
    TSort{}   -> Set.empty
    TErased{} -> Set.empty
    TError{}  -> Set.empty
    TVar i         -> Set.singleton i
    TApp f ts      -> freeVars (f, ts)
    TLam b         -> freeVars (Binder 1 b)
    TLet e b       -> freeVars (e, Binder 1 b)
    TCase i _ d bs -> freeVars (i, (d, bs))

instance HasFree TAlt where
  freeVars a = case a of
    TACon _ i b -> freeVars (Binder i b)
    TALit _ b   -> freeVars b
    TAGuard g b -> freeVars (g, b)

