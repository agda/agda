-- Andreas, 2026-10-03, issue #8171, reported by Andreas Abel
-- Giving a term mentioning a strictly positive variable failed.

{-# OPTIONS --polarity #-}

mutual
  data Cxt : Set where
    ε    : Cxt
    _>_ : (Γ : Cxt) (a : Ty Γ) → Cxt

  data Ty (Γ : Cxt) : Set where
    μ : (d : Desc Γ) → Ty Γ

  data Desc (Γ : Cxt) : Set where
    ι   : _  -- done
    ch  : (d e : Desc Γ)                → _
    σ   : (a : Ty Γ) (d : Desc (Γ > a)) → _
    δ   : (d : Desc Γ)                  → _
    inf : (b : Ty Γ) (d : Desc Γ)       → _

variable
  Γ : Cxt
  a : Ty Γ

record ⊤ : Set where

record Σ (@++ A : Set) (@++ B : A → Set) : Set where
  constructor _,_
  field proj₁ : A
        proj₂ : B proj₁

data _⊎_ (@++ A B : Set) : Set where
  inj₁ : A → A ⊎ B
  inj₂ : B → A ⊎ B

data Mu (F : @++ Set → Set) : Set where
  intro : F (Mu F) → Mu F

mutual
  data Env : Cxt → Set₁ where
    ε   : Env ε
    _>_ : (ρ : Env Γ) (v : ⟦ a ⟧ ρ) → Env (Γ > a)

  ⟦_⟧ : Ty Γ → Env Γ → Set
  ⟦ μ d ⟧ ρ = Mu (D⟦ d ⟧ ρ)

  D⟦_⟧ : (d : Desc Γ) (ρ : Env Γ) → @++ Set → Set
  D⟦ ι        ⟧ ρ X = ⊤
  D⟦ ch d₁ d₂ ⟧ ρ X = {!D⟦ d₁ ⟧ ρ X ⊎ D⟦ d₂ ⟧ ρ X!}
  D⟦ σ a d    ⟧ ρ X = {!Σ (⟦ a ⟧ ρ) λ v → D⟦ d ⟧ (ρ > v) X!}
  D⟦ δ d      ⟧ ρ X = {!Σ X λ _ → D⟦ d ⟧ ρ X!}
  D⟦ inf b d  ⟧ ρ X = {!Σ ((v : ⟦ b ⟧ ρ) → X) λ _ → D⟦ d ⟧ ρ X !}
