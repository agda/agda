
open import Agda.Primitive

record Order {ℓ} ℓ' (A : Set ℓ) : Set (ℓ ⊔ lsuc ℓ') where
  field
    _≤_ : A → A → Set ℓ'
open Order {{...}} public

data ℕ : Set where
  Zero : ℕ
  Succ : ℕ → ℕ

data _≤ⁿ_ : ℕ → ℕ → Set where
  Zero : ∀ {n} → Zero ≤ⁿ n
  Succ : ∀ {n₁ n₂} → n₁ ≤ⁿ n₂ → Succ n₁ ≤ⁿ Succ n₂

instance
  Order[ℕ] : Order lzero ℕ
  Order[ℕ] = record { _≤_ = _≤ⁿ_ }

subtract : ∀ (n₁ n₂ : ℕ) → n₂ ≤ n₁ → ℕ
subtract   n₁      .Zero      Zero    = n₁
subtract .(Succ _) .(Succ _) (Succ P) = subtract _ _ P

