
record R₁ : Set₁ where
  field
    A : Set

open R₁ ⦃ … ⦄

record R₂ : Set₁ where
  field
    ⦃ r₁ ⦄ : R₁

  B : Set
  B = A
