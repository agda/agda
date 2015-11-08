-- {-# OPTIONS --show-implicit #-}
-- {-# OPTIONS -v tc.meta:25 #-}
module NoBlockOnLevel where

open import Common.Level
open import Common.Product

BSetoid : ∀ c → Set (lsuc c)
BSetoid c = Set c

infixr 0 _⟶_

postulate
  _⟶_ : ∀ {f t} → BSetoid f → BSetoid t → Set (f ⊔ t)
  →-to-⟶ : ∀ {a b} {A : Set a} {B : BSetoid b} →
           (A → B) → A ⟶ B

postulate
  a b p : Level
  A : Set a
  B : Set b
  P : A → B → Set p

-- This will leave unsolved metas if we give up on an unsolved level constraint
-- when checking argument spines. Since we can't match on levels it's safe to keep
-- checking later constraints even if they depend on the unsolved levels.
f : (∃ λ x → ∃ λ y → P x y) ⟶ (∃ λ y → ∃ λ x → P x y)
f = →-to-⟶ λ p → proj₁ (proj₂ p) , proj₁ p , proj₂ (proj₂ p)

