module TelescopingLet3 where

module Star where
  ★ : Set₁
  ★ = Set

  ★₁ : Set₂
  ★₁ = Set₁

module MEndo (open Star) (A : ★) where
  Endo = A → A

-- at this point, ★ should no longer be in scope

data D3 (open Star using (★₁)) : ★₁ where
  c : (A : ★) → D3
-- ★₁ is in scope
-- ★ is not in scope since it was not brought in scope
-- (not included in the using ())
