------------------------------------------------------------------------
-- Products implemented using records
------------------------------------------------------------------------

{-# OPTIONS --universe-polymorphism #-}

-- It it ever becomes convenient to pattern match on records I might
-- make this the default implementation of products.

module Data.Product.Record where

open import Function
open import Level

infixr 4 _,_
infixr 2 _×_ _-×-_ _-,-_

------------------------------------------------------------------------
-- Definition

record Σ {a b} (A : Set a) (B : A → Set b) : Set (a ⊔ b) where
  constructor _,_
  field
    proj₁ : A
    proj₂ : B proj₁

open Σ public

_×_ : ∀ {a b} (A : Set a) (B : Set b) → Set (a ⊔ b)
A × B = Σ A (λ _ → B)

------------------------------------------------------------------------
-- Functions

<_,_> : ∀ {a b c} {A : Set a} {B : A → Set b} {C : ∀ {x} → B x → Set c}
        (f : (x : A) → B x) → ((x : A) → C (f x)) →
        ((x : A) → Σ (B x) C)
< f , g > x = (f x , g x)

map : ∀ {a b p q}
        {A : Set a} {B : Set b} {P : A → Set p} {Q : B → Set q} →
      (f : A → B) → (∀ {x} → P x → Q (f x)) →
      Σ A P → Σ B Q
map f g = < f ∘ proj₁ , g ∘ proj₂ >

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
