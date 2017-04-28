-- Andreas, 2017-04-28, issue #2558 reported by Youyou Cong
-- Size solver assumed invariants that do not hold.

open import Common.Size

data Con (i : Size) : Set where
  c : {j : Size< i} → Con i  -- needed

postulate
  Tms : {i j : Size} → Con i → Con j → Set
  Ty  : (i : Size) {j : Size< i} → Con j → Set

  sub : ∀{i}{j k : Size< i} {l : Size< j} {Γ : Con k} {Δ : Con l} →
          Tms Γ Δ → Ty j Δ → Ty i Γ

  P   : ∀{A : Set} (a : A) → Set

  [][]T : {i : Size} {j : Size< i} {k : Size< ↑ i} {l : Size< ↑ (↑ i)}
          {Γ : Con l} {Δ : Con k} {Σ : Con j} {A : Ty i Σ} →
          (δ : Tms Δ Σ) →
          (σ : Tms Γ Δ) →  -- Γ needed
          P (sub σ (sub δ A))  -- sub σ needed

-- Should pass
