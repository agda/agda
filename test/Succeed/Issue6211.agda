{-# OPTIONS --cubical #-}

open import Agda.Primitive

_∘_ :
  ∀ {a b c} {A : Set a} {B : Set b} {C : Set c} →
  (B → C) → (A → B) → (A → C)
(f ∘ g) x = f (g x)

postulate
  F : ∀ {a} (A : Set a) → A → Set a

variable
  a : Level
  A : Set a

postulate
  _ : (f : A → A) → F ((_ → A) → _) (_∘ f)
