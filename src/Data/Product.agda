------------------------------------------------------------------------
-- Products
------------------------------------------------------------------------

module Data.Product where

open import Data.Function
open import Relation.Nullary.Core

infixr 4 _,_
infix  4 ,_
infixr 2 _×_ _-×-_ _-,-_

------------------------------------------------------------------------
-- Definition

data Σ (A : Set) (B : A → Set) : Set where
  _,_ : (x : A) (y : B x) → Σ A B

∃ : {A : Set} → (A → Set) → Set
∃ = Σ _

∄ : {A : Set} → (A → Set) → Set
∄ P = ¬ ∃ P

∃₂ : {A : Set} {B : A → Set} (C : (x : A) → B x → Set) → Set
∃₂ C = ∃ λ a → ∃ λ b → C a b

_×_ : (A B : Set) → Set
A × B = Σ A (λ _ → B)

------------------------------------------------------------------------
-- Functions

-- Sometimes the first component can be inferred.

,_ : ∀ {A} {B : A → Set} {x} → B x → ∃ B
, y = _ , y

proj₁ : ∀ {A B} → Σ A B → A
proj₁ (x , y) = x

proj₂ : ∀ {A B} → (p : Σ A B) → B (proj₁ p)
proj₂ (x , y) = y

<_,_> : ∀ {A} {B : A → Set} {C : ∀ {x} → B x → Set}
        (f : (x : A) → B x) → ((x : A) → C (f x)) →
        ((x : A) → Σ (B x) C)
< f , g > x = (f x , g x)

map : ∀ {A B P Q} →
      (f : A → B) → (∀ {x} → P x → Q (f x)) →
      Σ A P → Σ B Q
map f g = < f ∘ proj₁ , g ∘ proj₂ >

zip : ∀ {A B C P Q R} →
      (_∙_ : A → B → C) →
      (∀ {x y} → P x → Q y → R (x ∙ y)) →
      Σ A P → Σ B Q → Σ C R
zip _∙_ _∘_ p₁ p₂ = (proj₁ p₁ ∙ proj₁ p₂ , proj₂ p₁ ∘ proj₂ p₂)

swap : ∀ {A B} → A × B → B × A
swap = < proj₂ , proj₁ >

_-×-_ : ∀ {A B} → (A → B → Set) → (A → B → Set) → (A → B → Set)
f -×- g = f -[ _×_ ]₁- g

_-,-_ : ∀ {A B C D} → (A → B → C) → (A → B → D) → (A → B → C × D)
f -,- g = f -[ _,_ ]- g

curry : {A : Set} {B : A → Set} {C : Σ A B → Set} →
        ((p : Σ A B) → C p) →
        ((x : A) → (y : B x) → C (x , y))
curry f x y = f (x , y)

uncurry : {A : Set} {B : A → Set} {C : Σ A B → Set} →
          ((x : A) → (y : B x) → C (x , y)) →
          ((p : Σ A B) → C p)
uncurry f (p₁ , p₂) = f p₁ p₂
