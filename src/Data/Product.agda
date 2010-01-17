------------------------------------------------------------------------
-- Products
------------------------------------------------------------------------

{-# OPTIONS --universe-polymorphism #-}

module Data.Product where

open import Function
open import Level
open import Relation.Nullary

infixr 4 _,_ _,′_
infix  4 ,_
infixr 2 _×_ _-×-_ _-,-_

------------------------------------------------------------------------
-- Definition

record Σ {a b} (A : Set a) (B : A → Set b) : Set (a ⊔ b) where
  constructor _,_
  field
    proj₁ : A
    proj₂ : B proj₁

open Σ public

∃ : ∀ {a b} {A : Set a} → (A → Set b) → Set (a ⊔ b)
∃ = Σ _

∄ : ∀ {a b} {A : Set a} → (A → Set b) → Set (a ⊔ b)
∄ P = ¬ ∃ P

∃₂ : ∀ {a b c} {A : Set a} {B : A → Set b}
     (C : (x : A) → B x → Set c) → Set (a ⊔ b ⊔ c)
∃₂ C = ∃ λ a → ∃ λ b → C a b

_×_ : ∀ {a b} (A : Set a) (B : Set b) → Set (a ⊔ b)
A × B = Σ A (λ _ → B)

_,′_ : ∀ {a b} {A : Set a} {B : Set b} → A → B → A × B
_,′_ = _,_

------------------------------------------------------------------------
-- Unique existence

-- Parametrised on the underlying equality.

∃! : ∀ {a b ℓ} {A : Set a} →
     (A → A → Set ℓ) → (A → Set b) → Set (a ⊔ b ⊔ ℓ)
∃! _≈_ B = ∃ λ x → B x × (∀ {y} → B y → x ≈ y)

------------------------------------------------------------------------
-- Functions

-- Sometimes the first component can be inferred.

,_ : ∀ {a b} {A : Set a} {B : A → Set b} {x} → B x → ∃ B
, y = _ , y

<_,_> : ∀ {a b c} {A : Set a} {B : A → Set b} {C : ∀ {x} → B x → Set c}
        (f : (x : A) → B x) → ((x : A) → C (f x)) →
        ((x : A) → Σ (B x) C)
< f , g > x = (f x , g x)

map : ∀ {a b p q}
        {A : Set a} {B : Set b} {P : A → Set p} {Q : B → Set q} →
      (f : A → B) → (∀ {x} → P x → Q (f x)) →
      Σ A P → Σ B Q
map f g = < f ∘ proj₁ , g ∘ proj₂ >

zip : ∀ {a b c p q r}
        {A : Set a} {B : Set b} {C : Set c}
        {P : A → Set p} {Q : B → Set q} {R : C → Set r} →
      (_∙_ : A → B → C) →
      (∀ {x y} → P x → Q y → R (x ∙ y)) →
      Σ A P → Σ B Q → Σ C R
zip _∙_ _∘_ p₁ p₂ = (proj₁ p₁ ∙ proj₁ p₂ , proj₂ p₁ ∘ proj₂ p₂)

swap : ∀ {a b} {A : Set a} {B : Set b} → A × B → B × A
swap = < proj₂ , proj₁ >

_-×-_ : ∀ {a b i j} {A : Set a} {B : Set b} →
        (A → B → Set i) → (A → B → Set j) → (A → B → Set _)
f -×- g = f -[ _×_ ]- g

_-,-_ : ∀ {a b c d} {A : Set a} {B : Set b} {C : Set c} {D : Set d} →
        (A → B → C) → (A → B → D) → (A → B → C × D)
f -,- g = f -[ _,_ ]- g

curry : ∀ {a b c} {A : Set a} {B : A → Set b} {C : Σ A B → Set c} →
        ((p : Σ A B) → C p) →
        ((x : A) → (y : B x) → C (x , y))
curry f x y = f (x , y)

uncurry : ∀ {a b c} {A : Set a} {B : A → Set b} {C : Σ A B → Set c} →
          ((x : A) → (y : B x) → C (x , y)) →
          ((p : Σ A B) → C p)
uncurry f p = f (proj₁ p) (proj₂ p)

uncurry′ : ∀ {a b c} {A : Set a} {B : Set b} {C : Set c} →
           (A → B → C) → (A × B → C)
uncurry′ = uncurry
