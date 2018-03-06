------------------------------------------------------------------------
-- The Agda standard library
--
-- Products
------------------------------------------------------------------------

module Data.Product where

open import Function
open import Level
open import Relation.Nullary
open import Agda.Builtin.Equality

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

-- The syntax declaration below is attached to Σ-syntax, to make it
-- easy to import Σ without the special syntax.

infix 2 Σ-syntax

Σ-syntax : ∀ {a b} (A : Set a) → (A → Set b) → Set (a ⊔ b)
Σ-syntax = Σ

syntax Σ-syntax A (λ x → B) = Σ[ x ∈ A ] B

∃ : ∀ {a b} {A : Set a} → (A → Set b) → Set (a ⊔ b)
∃ = Σ _

∃-syntax : ∀ {a b} {A : Set a} → (A → Set b) → Set (a ⊔ b)
∃-syntax = ∃

syntax ∃-syntax (λ x → B) = ∃[ x ] B

∄ : ∀ {a b} {A : Set a} → (A → Set b) → Set (a ⊔ b)
∄ P = ¬ ∃ P

∄-syntax : ∀ {a b} {A : Set a} → (A → Set b) → Set (a ⊔ b)
∄-syntax = ∄

syntax ∄-syntax (λ x → B) = ∄[ x ] B

∃₂ : ∀ {a b c} {A : Set a} {B : A → Set b}
     (C : (x : A) → B x → Set c) → Set (a ⊔ b ⊔ c)
∃₂ C = ∃ λ a → ∃ λ b → C a b

_×_ : ∀ {a b} (A : Set a) (B : Set b) → Set (a ⊔ b)
A × B = Σ[ x ∈ A ] B

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
map f g (x , y) = (f x , g y)

zip : ∀ {a b c p q r}
        {A : Set a} {B : Set b} {C : Set c}
        {P : A → Set p} {Q : B → Set q} {R : C → Set r} →
      (_∙_ : A → B → C) →
      (∀ {x y} → P x → Q y → R (x ∙ y)) →
      Σ A P → Σ B Q → Σ C R
zip _∙_ _∘_ (a , p) (b , q) = ((a ∙ b) , (p ∘ q))

swap : ∀ {a b} {A : Set a} {B : Set b} → A × B → B × A
swap (x , y) = (y , x)

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

curry′ : ∀ {a b c} {A : Set a} {B : Set b} {C : Set c} →
         (A × B → C) → (A → B → C)
curry′ = curry

uncurry : ∀ {a b c} {A : Set a} {B : A → Set b} {C : Σ A B → Set c} →
          ((x : A) → (y : B x) → C (x , y)) →
          ((p : Σ A B) → C p)
uncurry f (x , y) = f x y

uncurry′ : ∀ {a b c} {A : Set a} {B : Set b} {C : Set c} →
           (A → B → C) → (A × B → C)
uncurry′ = uncurry
