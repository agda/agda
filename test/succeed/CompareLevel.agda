{-# OPTIONS --universe-polymorphism #-}
module CompareLevel where

open import Common.Level

postulate
  X : Set
  Foo : (a b : Level) → Set (a ⊔ b) → Set
  Bar : Foo _ _ X  -- solve _1 ⊔ _2 = 0

postulate
  id    : ∀ {a}{A : Set a} → A → A
  apply : ∀ {a b} {A : Set a} {B : Set b} (f : A → B) → A → B
  a b   : Level
  Any   : (ℓ : Level) → Set ℓ
  any   : ∀ {ℓ} → Any ℓ

-- Too aggressive level solving can cause a problem here.
foo : Any (a ⊔ b)
foo =
  apply {_}{_} id any
