-- 2018-09-05, reported by Andreas Abel
-- The new type-directed rewriting was using the wrong type for
-- constructors of parametrized datatypes.

{-# OPTIONS --rewriting #-}

module _ (Form : Set) where

open import Agda.Builtin.Equality
{-# BUILTIN REWRITE _≡_ #-}

data Cxt : Set where
  _∙_ : (Γ : Cxt) (A : Form) → Cxt

data _≤_ : (Γ Δ : Cxt) → Set where
  id≤ : ∀{Γ} → Γ ≤ Γ
  lift : ∀{A Γ Δ} (τ : Γ ≤ Δ) → (Γ ∙ A) ≤ (Δ ∙ A)

postulate
  lift-id≤ : ∀{Γ A} → lift id≤ ≡ id≤ {Γ ∙ A}

{-# REWRITE lift-id≤ #-}

_•_ : ∀{Γ Δ Φ} (τ : Γ ≤ Δ) (σ : Δ ≤ Φ) → Γ ≤ Φ
id≤ • σ = σ
lift τ • id≤ = lift τ
lift τ • lift σ = lift (τ • σ)
