{-# OPTIONS --universe-polymorphism #-}

module Issue333 where

open import Common.Level

data Σ a b (A : Set a) (B : A → Set b) : Set (a ⊔ b) where
  _,_ : (x : A) → B x → Σ a b A B

P : ∀ a b (A : Set a) (B : Set b) → Set (a ⊔ b)
P a b A B = Σ a b A (λ _ → B)

postulate
  A B : Set
  foo : Σ lzero lzero A λ (y : A) → P lzero lzero A B

bar : Set₁
bar = helper foo
  where
  helper : (Σ _ _ A λ (y : A) → P _ _ _ _) → Set₁
  helper (y , (x⇓ , fy⇑)) = Set
