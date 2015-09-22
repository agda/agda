-- 2012-03-15, example by Nisse
module Issue585-11 where

data D₁ : Set where
  d₁ : D₁

f₁ : D₁ → D₁ → D₁
f₁ x d₁ = x

data D₂ : Set where
  d₂ : D₂ → D₂

postulate
  P  : D₁ → Set
  f₂ : ∀ {n₁ n₂} → P n₁ → P n₂ → P (f₁ n₁ n₂)

mutual

  f₃ : D₁ → D₂ → D₁
  f₃ _ (d₂ _) = _

  f₄ : ∀ {n} → P n → (i : D₂) → P (f₃ n i)
  f₄ p (d₂ i) = f₂ p (f₄ p i)

-- This worked until Agda 2.3.0
-- Now, recursive solutions  [here: f₃ n (d₂ i) = f₁ n (f₃ n i)]
-- are no longer found, since termination is not be guaranteed by the occurs check.
