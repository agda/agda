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

<_,_> : ∀ {a b c} → (a → b) → (a → c) → (a → b × c)
< f , g > x = f x , g x

map-× : ∀ {a b c d} → (a → c) → (b → d) → (a × b → c × d)
map-× f g = < f ∘ proj₁ , g ∘ proj₂ >

swap : ∀ {a b} → a × b → b × a
swap = < proj₂ , proj₁ >

_-×-_ : ∀ {a b} → (a → b → Set) → (a → b → Set) → (a → b → Set)
f -×- g = f -[ _×_ ]₁- g

_-,-_ : ∀ {a b c d} → (a → b → c) → (a → b → d) → (a → b → c × d)
f -,- g = f -[ _,_ ]- g

Σ-curry : {a : Set} {b : a → Set} {c : Σ a b → Set} →
          ((p : Σ a b) → c p) →
          ((x : a) → (y : b x) → c (x , y))
Σ-curry f x y = f (x , y)

Σ-uncurry : {a : Set} {b : a → Set} {c : Σ a b → Set} →
            ((x : a) → (y : b x) → c (x , y)) →
            ((p : Σ a b) → c p)
Σ-uncurry f p = f (proj₁ p) (proj₂ p)

curry : ∀ {a b c} → (a × b → c) → (a → b → c)
curry = Σ-curry

uncurry : ∀ {a b c} → (a → b → c) → (a × b → c)
uncurry = Σ-uncurry
