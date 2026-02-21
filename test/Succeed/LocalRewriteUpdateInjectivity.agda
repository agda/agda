{-# OPTIONS --local-rewriting #-}

open import Agda.Builtin.Equality
open import Agda.Builtin.Equality.Rewrite
open import Agda.Builtin.List renaming (_∷_ to _,-_)

-- Based on #8218
module LocalRewriteUpdateInjectivity where

map : {A B : Set} → (A → B) → List A → List B
map f []        = []
map f (x ,- xs) = f x ,- map f xs

module _ (_++_ : ∀{A : Set} → List A → List A → List A)
         (@rew map-++ : ∀ {A B : Set} (f : A → B) xs ys
                      → map f (xs ++ ys) ≡ map f xs ++ map f ys)
         where

  data Ty : Set where
    _⟶_ : List Ty → Ty → Ty

  data Exp (Γ : List Ty) : Ty → Set where
    lamMany : ∀{τ} (τs : List Ty) → Exp (τs ++ Γ) τ → Exp Γ (τs ⟶ τ)

  {-# TERMINATING #-}
  desugarTy : Ty → Ty
  desugarTy (τs ⟶ τ) = map desugarTy τs ⟶ desugarTy τ

  desugarExp : ∀{Γ τ} → Exp Γ τ → Exp (map desugarTy Γ) (desugarTy τ)
  desugarExp (lamMany τs x) = lamMany (map desugarTy τs) (desugarExp x)
