{-# OPTIONS --prop #-}

data Squash {ℓ} (A : Set ℓ) : Prop ℓ where
  squash : A → Squash A

squash-elim : ∀ {ℓ₁ ℓ₂} (A : Set ℓ₁) (P : Prop ℓ₂)
            → (A → P) → Squash A → P
squash-elim A P f (squash x) = f x
