-- Andreas, 2025-11-12, issue #2500 was fixed in 2.6.1

module Issue2500 where

data ⊤ : Set where
  tt : ⊤

flip : ∀ {t₁ t₂ t₃ : Set} → (t₁ → t₂ → t₃) → t₂ → t₁ → t₃
flip f x y = f y x

module IdenticalSnowFlake where

  record R : Set₁ where
    field
      f : ∀ {a b c : Set} → {{_ : ⊤}} → (a → b) → (b → c) → ⊤

    g : ∀ {a b c : Set} → (b → c) → (a → b) → ⊤
    g = flip (f {{tt}})

    field
      top : ⊤

module Ulf where

  R : Set₁
  R = (f : ∀ {a b c : Set} → {{_ : ⊤}} → (a → b) → (b → c) → ⊤)
      (let g : ∀ {a b c : Set} → (b → c) → (a → b) → ⊤
           g = flip (f {{tt}})) →
      Set

-- Error was:
-- _t₂_20 → _t₁_19 → _t₃_21 != {a b c : Set} → (b → c) → (a → b) → ⊤
-- because one is an implicit function type and the other is an
-- explicit function type
-- when checking that the inferred type of an application
--   _t₂_20 → _t₁_19 → _t₃_21
-- matches the expected type
--   {a b c : Set} → (b → c) → (a → b) → ⊤

-- Should succeed.
