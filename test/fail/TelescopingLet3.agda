module TelescopingLet3 where

module Star where
  ★ : Set₁
  ★ = Set

  ★₁ : Set₂
  ★₁ = Set₁

module MEndo (open Star) (A : ★) where
  Endo = A → A

data D3 (open Star using (★₁)) : ★₁ where
  c : (A : ★) → D3
