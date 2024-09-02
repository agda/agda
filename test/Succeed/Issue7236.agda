-- Andreas, 2024-04-24, issue #7236
-- Regression in higher-order rewriting
-- introduced by commit 031c69df6ca2e4ae203a5809df0277c587f4f1a4
-- Date:   Thu May 31 10:46:49 2018 +0200
-- [ rewriting ] Make non-linear matching more type-directed
--
-- Problem: uses telescope for lambda-bound variables in higher-order pattern
-- where a context would be correct.

{-# OPTIONS --rewriting #-}

-- {-# OPTIONS -v rewriting:60 #-}

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; _∷_)

postulate
  ANY : {A : Set} → A

data Ty : Set where
    arr : Ty → Ty → Ty

Ctx : Set
Ctx = List Ty

data Idx : Ctx → Ty → Set where
    zero : {Γ : Ctx} {τ : Ty} → Idx (τ ∷ Γ) τ
    suc : {Γ : Ctx} {τ₁ τ₂ : Ty} → Idx Γ τ₂ → Idx (τ₁ ∷ Γ) τ₂

data Expr (Γ : Ctx) : Ty → Set where
    var : {τ : Ty} → Idx Γ τ → Expr Γ τ
    abstraction : {τ₁ τ₂ : Ty} → Expr (τ₁ ∷ Γ) τ₂ → Expr Γ (Ty.arr τ₁ τ₂)

module Rename where

    Rename : Ctx → Ctx → Set
    Rename Γ Γ' = {τ : Ty} → Idx Γ τ → Idx Γ' τ

    cons : {Γ Γ' : Ctx} {τ : Ty} → Idx Γ' τ → Rename Γ Γ' → Rename (τ ∷ Γ) Γ'
    cons idx ρ Idx.zero = idx
    cons idx ρ (Idx.suc idx') = ρ idx'

    ext : {Γ Γ' : Ctx} {τ : Ty} → Rename Γ Γ' → Rename (τ ∷ Γ) (τ ∷ Γ')
    ext ρ = cons Idx.zero (λ x → Idx.suc (ρ x))

    rename : {Γ Γ' : Ctx} {τ : Ty} → Rename Γ Γ' → Expr Γ τ → Expr Γ' τ
    rename ρ (Expr.var idx) = Expr.var (ρ idx)
    rename ρ (Expr.abstraction e) = Expr.abstraction (rename (ext ρ) e)

open Rename using (Rename)

Subst : Ctx → Ctx → Set
Subst Γ Γ' = {τ : Ty} → Idx Γ τ → Expr Γ' τ

infixr 6 _•_
_•_ : {Γ Γ' : Ctx} {τ : Ty} → Expr Γ' τ → Subst Γ Γ' → Subst (τ ∷ Γ) Γ'
_•_ e σ Idx.zero = e
_•_ e σ (Idx.suc idx) = σ idx

⟰ : {Γ Γ' : Ctx} {τ : Ty} → Subst Γ Γ' → Subst Γ (τ ∷ Γ')
⟰ σ idx = Rename.rename Idx.suc (σ idx)

ext : {Γ Γ' : Ctx} {τ : Ty} → Subst Γ Γ' → Subst (τ ∷ Γ) (τ ∷ Γ')
ext σ = Expr.var Idx.zero • ⟰ σ


subst : {Γ Γ' : Ctx} {τ : Ty} (σ : Subst Γ Γ') → Expr Γ τ → Expr Γ' τ
subst σ (Expr.var idx) = σ idx
subst σ (Expr.abstraction e) = Expr.abstraction (subst (ext σ) e)

ren : {Γ Γ' : Ctx} → Rename Γ Γ' → Subst Γ Γ'
ren ρ x = Expr.var (ρ x)

postulate

    comp : {Γ Γ' Γ'' : Ctx} → Subst Γ Γ' → Subst Γ' Γ'' → Subst Γ Γ''
    -- (σ ； σ') x = subst σ' (σ x)

    seq-def : {Γ Γ' Γ'' : Ctx} {τ : Ty} (σ : Subst Γ Γ') (σ' : Subst Γ' Γ'') (idx : Idx Γ τ) → comp σ σ' idx ≡ subst σ' (σ idx)
    -- seq-def σ σ' idx = refl

{-# BUILTIN REWRITE _≡_ #-}
{-# REWRITE seq-def #-}

subst-ren : {Γ Γ' Γ'' : Ctx} {τ : Ty} (ρ : Rename Γ' Γ'') (σ : Subst Γ Γ') (e : Expr Γ τ) → subst (ren ρ) (subst σ e) ≡ subst (comp σ (ren ρ)) e
subst-ren ρ σ (Expr.var idx) =  refl
subst-ren ρ σ (Expr.abstraction e) with subst-ren (Rename.ext ρ) (ext σ) e
... | x = ANY

-- Error was:
--
--   Expected a hidden argument, but found a visible argument
--   when checking that the type
--   ...
--   ≡
--   abstraction
--   (subst
--    (var zero •
--     (λ idx → Rename.rename suc (subst (λ z {τ} → var (ρ τ)) (σ idx))))
--    e)
--   of the generated with function is well-formed
--
-- Rewriting was faulty:
--
--   rewrote  comp σ (ren ρ) idx
--        to  subst (λ z {τ} → var (ρ τ)) (σ idx)
--
-- Now:
--
--   rewrote  comp σ (ren ρ) idx
--        to  subst (λ {τ} z → var (ρ z)) (σ idx)
--
-- Should succeed.
