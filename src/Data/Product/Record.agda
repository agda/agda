------------------------------------------------------------------------
-- Products implemented using records
------------------------------------------------------------------------

-- It it ever becomes convenient to pattern match on records I might
-- make this the default implementation of products.

module Data.Product.Record where

open import Data.Function

infixr 4 _,_
infixr 2 _×_ _-×-_ _-,-_

------------------------------------------------------------------------
-- Definition

record Σ (A : Set) (B : A → Set) : Set where
  constructor _,_
  field
    proj₁ : A
    proj₂ : B proj₁

open Σ public

_×_ : (a b : Set) → Set
a × b = Σ a (λ _ → b)

------------------------------------------------------------------------
-- Functions

<_,_> : {A : Set} {B : A → Set} {C : ∀ {x} → B x → Set}
        (f : (x : A) → B x) → ((x : A) → C (f x)) →
        ((x : A) → Σ (B x) C)
< f , g > x = (f x , g x)

map : ∀ {A B P Q} →
      (f : A → B) → (∀ {x} → P x → Q (f x)) →
      Σ A P → Σ B Q
map f g = < f ∘ proj₁ , g ∘ proj₂ >

swap : ∀ {a b} → a × b → b × a
swap = < proj₂ , proj₁ >

_-×-_ : {A B : Set} → (A → B → Set) → (A → B → Set) → (A → B → Set)
f -×- g = f -[ _×_ ]- g

_-,-_ : {A B C D : Set} → (A → B → C) → (A → B → D) → (A → B → C × D)
f -,- g = f -[ _,_ ]- g

curry : {a : Set} {b : a → Set} {c : Σ a b → Set} →
        ((p : Σ a b) → c p) →
        ((x : a) → (y : b x) → c (x , y))
curry f x y = f (x , y)

uncurry : {a : Set} {b : a → Set} {c : Σ a b → Set} →
          ((x : a) → (y : b x) → c (x , y)) →
          ((p : Σ a b) → c p)
uncurry f p = f (proj₁ p) (proj₂ p)
