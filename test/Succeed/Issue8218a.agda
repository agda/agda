{-# OPTIONS --rewriting #-}

open import Issue8218ListUtils
open import Agda.Builtin.Equality
open import Agda.Builtin.Equality.Rewrite

{-# REWRITE map-++ #-}

data Ty : Set where
  _⟶_ : List Ty → Ty → Ty

data Exp (Γ : List Ty) : Ty → Set where
  lamMany : ∀{τ} (τs : List Ty) → Exp (τs ++ Γ) τ → Exp Γ (τs ⟶ τ)

{-# TERMINATING #-}
desugarTy : Ty → Ty
desugarTy (τs ⟶ τ) = map desugarTy τs ⟶ desugarTy τ

desugarExp : ∀{Γ τ} → Exp Γ τ → Exp (map desugarTy Γ) (desugarTy τ)
desugarExp (lamMany τs x) = lamMany (map desugarTy τs) (desugarExp x)
