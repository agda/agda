{-# LANGUAGE MultiParamTypeClasses #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}

module Agda.Compiler.Treeless.Subst where

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
          where rho' = liftS 1 rho

instance Subst TTerm TAlt where
  applySubst rho (TACon c i b)  = TACon c i (applySubst (liftS i rho) b)
  applySubst rho (TALit l b)  = TALit l (applySubst rho b)
  applySubst rho (TAPlus k b) = TAPlus k (applySubst (liftS 1 rho) b)
