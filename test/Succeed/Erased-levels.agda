{-# OPTIONS --erasure --cubical-compatible --guardedness --prop
            --two-level #-}

open import Agda.Builtin.Coinduction
open import Agda.Builtin.Equality
open import Agda.Builtin.Sigma
open import Agda.Primitive

Set′ : (@0 a : Level) → Set (lsuc a)
Set′ a = Set a

Prop′ : (@0 a : Level) → Set (lsuc a)
Prop′ a = Prop a

SSet′ : (@0 a : Level) → SSet (lsuc a)
SSet′ a = SSet a

F : ∀ {@0 a} → (Set a → Set a) → Set (lsuc a)
F G = Σ _ G

subst :
  ∀ {@0 a p} {@0 A : Set a} {x y : A}
  (P : A → Set p) → x ≡ y → P x → P y
subst _ refl p = p

♯′ : ∀ {@0 a} {A : Set a} → A → ∞ A
♯′ x = ♯ x
