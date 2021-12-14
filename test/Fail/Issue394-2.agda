postulate
  A : Set
  F : (A : Set₁) → (A → A → Set) → Set

syntax F A (λ x y → B) = y , y ⟨ A ∼ B ⟩ x
