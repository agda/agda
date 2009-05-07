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

record Σ (a : Set) (b : a → Set) : Set where
  field
    proj₁ : a
    proj₂ : b proj₁

open Σ public

_×_ : (a b : Set) → Set
a × b = Σ a (λ _ → b)

------------------------------------------------------------------------
-- Functions

_,_ : ∀ {a b} → (x : a) → b x → Σ a b
(x , y) = record {proj₁ = x; proj₂ = y}

<_,_> : ∀ {A} {B : A → Set} {C : ∀ {x} → B x → Set}
        (f : (x : A) → B x) → ((x : A) → C (f x)) →
        ((x : A) → Σ (B x) C)
< f , g > x = (f x , g x)

map : ∀ {A B P Q} →
      (f : A → B) → (∀ {x} → P x → Q (f x)) →
      Σ A P → Σ B Q
map f g = < f ∘ proj₁ , g ∘ proj₂ >

swap : ∀ {a b} → a × b → b × a
swap = < proj₂ , proj₁ >

_-×-_ : ∀ {a b} → (a → b → Set) → (a → b → Set) → (a → b → Set)
f -×- g = f -[ _×_ ]₁- g

_-,-_ : ∀ {a b c d} → (a → b → c) → (a → b → d) → (a → b → c × d)
f -,- g = f -[ _,_ ]- g

curry : {a : Set} {b : a → Set} {c : Σ a b → Set} →
        ((p : Σ a b) → c p) →
        ((x : a) → (y : b x) → c (x , y))
curry f x y = f (x , y)

uncurry : {a : Set} {b : a → Set} {c : Σ a b → Set} →
          ((x : a) → (y : b x) → c (x , y)) →
          ((p : Σ a b) → c p)
uncurry f p = f (proj₁ p) (proj₂ p)
