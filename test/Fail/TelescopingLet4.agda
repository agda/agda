module TelescopingLet4 where

module Star where
  ★ : Set₁
  ★ = Set

  ★₁ : Set₂
  ★₁ = Set₁

data D5 (open Star using (★₁)) : ★₁ where
