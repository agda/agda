{-# OPTIONS --rewriting #-}

open import Agda.Builtin.Equality
{-# BUILTIN REWRITE _≡_ #-}

module _ (Form : Set) where  -- FAILS
-- postulate Form : Set -- WORKS

data Cxt : Set where
  ε : Cxt
  _∙_ : (Γ : Cxt) (A : Form) → Cxt

data _≤_ : (Γ Δ : Cxt) → Set where
  id≤ : ∀{Γ} → Γ ≤ Γ
  weak : ∀{A Γ Δ} (τ : Γ ≤ Δ) → (Γ ∙ A) ≤ Δ
  lift : ∀{A Γ Δ} (τ : Γ ≤ Δ) → (Γ ∙ A) ≤ (Δ ∙ A)

postulate lift-id≤ : ∀{Γ A} → lift id≤ ≡ id≤ {Γ ∙ A}
{-# REWRITE lift-id≤ #-}
