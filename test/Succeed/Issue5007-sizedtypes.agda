{-# OPTIONS --sized-types #-}

open import Agda.Builtin.Equality
open import Agda.Builtin.Size

mutual

  data D (i : Size) : Set where
    c : D′ i → D i

  record D′ (i : Size) : Set where
    coinductive
    field
      force : (j : Size< i) → D j

data R (i : Size) : D ∞ → D ∞ → Set where
  c₁ : ∀ x y → R i (c x) (c y)
  c₂ : ∀ x y → R i (c x) y

postulate
  F : (x : D ∞) (x′ : D′ ∞) → x ≡ c x′ → Set₁

G : Size → Set₁
G i = Set
  where
  G′ :
    (x′ y′ : D ∞) (x y : D′ ∞) →
    R i (c x) y′ →
    R i x′ (c y) →
    x .D′.force _ {- ∞ -} ≡ x′ →
    Set₁
  G′ _ _ _ _ (c₁ x _) (c₂ u _) eq   = F _ {- x .D′.force ∞ -} u eq
  G′ _ _ _ _ (c₂ _ _) _        refl = Set
  G′ _ _ _ _ _        _        _    = Set
