postulate
  A : Set
  F : (A : Set₁) → (A → A → Set) → Set

syntax F A (λ x y → B) = A x B y
