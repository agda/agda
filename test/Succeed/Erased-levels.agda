{-# OPTIONS --erasure --prop --two-level #-}

open import Agda.Primitive

Set′ : (@0 a : Level) → Set (lsuc a)
Set′ a = Set a

Prop′ : (@0 a : Level) → Set (lsuc a)
Prop′ a = Prop a

SSet′ : (@0 a : Level) → SSet (lsuc a)
SSet′ a = SSet a

postulate
  Σ : ∀ {@0 a p} (A : Set a) (P : A → Set p) → Set (a ⊔ p)

F : ∀ {@0 a} → (Set a → Set a) → Set (lsuc a)
F G = Σ _ G
