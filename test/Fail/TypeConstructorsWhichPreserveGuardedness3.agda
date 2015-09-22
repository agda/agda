module TypeConstructorsWhichPreserveGuardedness3 where

record ⊤ : Set where

data _⊎_ (A B : Set) : Set where
  inj₁ : A → A ⊎ B
  inj₂ : B → A ⊎ B

-- This should not be allowed.

ℕ : Set
ℕ = ⊤ ⊎ ℕ
