module Issue267 where

data I : Set where
  c : I

postulate
  T : I → Set
  P : ∀ i → T i → Set
  R : ∀ i → (T i → Set) → Set
  r : ∀ i → R i (P i)

P′ : ∀ i → T i → Set
P′ c x = P c x

foo : ∀ i → R i (λ v → P′ i v)
foo c = ?
