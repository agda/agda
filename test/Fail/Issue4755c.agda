{-# OPTIONS --rewriting #-}

open import Agda.Builtin.Unit
open import Agda.Builtin.Equality
open import Agda.Builtin.Equality.Rewrite

data _⇨_ (A B : Set) : Set where
  Λ : (A → B) → (A ⇨ B)

_∙_ : {A B : Set} (f : A ⇨ B) (a : A) → B
(Λ f) ∙ a = f a

_∘_ : {A B C : Set} (g : B ⇨ C) (f : A ⇨ B) → (A ⇨ C)
_∘_ {A} {B} {C} g f = Λ {A} {C} (λ x → g ∙ (f ∙ x))

postulate
  Λη : {A B : Set} (f : A ⇨ B) → (Λ (λ x → f ∙ x)) ≡ f

{-# REWRITE Λη #-}

oops : {A B : Set} (f : ⊤ ⇨ B) → Set
oops {A} {B} f = {! _∘_ {A} {⊤} {B} f (Λ (λ _ → tt)) !}
