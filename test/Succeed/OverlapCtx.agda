module OverlapCtx where

open import Agda.Primitive
open import Agda.Builtin.Nat
open import Agda.Builtin.Sigma

data LTL (Γ : Nat) : Set where
  “⊥”   : LTL Γ
  _“R”_ : LTL Γ → LTL Γ → LTL Γ

“□”_ : ∀ {Γ} → LTL Γ → LTL Γ
“□” P = “⊥” “R” P

private variable
  Γ Δ : Nat
  φ ψ : LTL Γ

postulate Fin : Nat → Set

module Semantics {ℓ} (World : Set ℓ) (step : World → World) where

  private variable
    ρ : World → Fin Γ → Set
    w : World

  -- opaque
  --   _⊨_ : ∀ {Γ} → Monotone World (Subsets (Fin Γ)) × ⌞ World ⌟ → LTL Γ → Ω
  --   (ρ , w) ⊨ atom x = ρ .hom w x

  record Semantics (φ : LTL Γ) : Setω where
    constructor semantics
    no-eta-equality
    field
      {lvl} : Level
      Sem : (World → Fin Γ → Set) → World → Set lvl
      -- Sem-is-prop : ∀ {ρ w} → is-prop (Sem ρ w)
      -- sem : ∀ {ρ w} → ∣ (ρ , w) ⊨ φ ∣ ↔ Sem ρ w

  Sem : (φ : LTL Γ) → ⦃ _ : Semantics φ ⦄ → (World → Fin Γ → Set) → World → Set _
  Sem φ ⦃ e ⦄ = Semantics.Sem e

  postulate instance
    Semantics-Default : Semantics φ
    {-# INCOHERENT Semantics-Default #-}

    Semantics-R : ∀ {Γ} {φ ψ : LTL Γ} ⦃ _ : Semantics φ ⦄ ⦃ _ : Semantics ψ ⦄ → Semantics (φ “R” ψ)

    Semantics-□ : ∀ {Γ} {φ : LTL Γ} ⦃ _ : Semantics φ ⦄ → Semantics (“⊥” “R” φ)
    {-# OVERLAPPING Semantics-□ #-}

  {-
  WAS:
  Failed to solve the following constraints:
  Resolve instance argument _81 : Semantics {Γ} (“□” φ)
  Candidates
    [overlapping] Semantics-□ :
      {Γ = Γ₁ : Nat} {φ = φ₁ : LTL Γ₁} ⦃ _ : Semantics {Γ₁} φ₁ ⦄ →
      Semantics {Γ₁} (“⊥” “R” φ₁)
    Semantics-R :
      {Γ = Γ₁ : Nat} {φ = φ₁ : LTL Γ₁} {ψ : LTL Γ₁}
      ⦃ _ : Semantics {Γ₁} φ₁ ⦄ ⦃ _ : Semantics {Γ₁} ψ ⦄ →
      Semantics {Γ₁} (φ₁ “R” ψ)
    [incoherent] Semantics-Default :
      {φ.Γ : Nat} {φ = φ₁ : LTL φ.Γ} → Semantics {φ.Γ} φ₁
    (stuck)
  -}

  test : (φ : LTL Γ) → (World → Fin Γ → Set) → World → Set _
  test φ = Sem (“□” φ)
