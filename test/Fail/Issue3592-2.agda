postulate
  F : Set₁ → Set₁

data P : Set₁ → Set₁ where
  c : P (F (P Set)) → P Set
