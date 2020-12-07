{-# OPTIONS --no-main #-}

postulate
  easy : (A : Set₁) → A

record R₁ : Set₂ where
  field
    A : Set₁

record R₂ : Set₂ where
  field
    r₁ : R₁
    a  : R₁.A r₁

r₁ : R₁
r₁ .R₁.A = Set

r₂ : R₂
r₂ = λ where
  .R₂.r₁ → r₁
  .R₂.a  → easy _
