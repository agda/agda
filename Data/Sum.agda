------------------------------------------------------------------------
-- Sums (disjoint unions)
------------------------------------------------------------------------

module Data.Sum where

open import Data.Function

------------------------------------------------------------------------
-- Definition

infixr 1 _⊎_

data _⊎_ (A B : Set) : Set where
  inj₁ : (x : A) → A ⊎ B
  inj₂ : (y : B) → A ⊎ B

------------------------------------------------------------------------
-- Functions

[_,_] : ∀ {a b c} → (a → c) → (b → c) → (a ⊎ b → c)
[ f , g ] (inj₁ x) = f x
[ f , g ] (inj₂ y) = g y

map-⊎ : ∀ {a b c d} → (a → c) → (b → d) → (a ⊎ b → c ⊎ d)
map-⊎ f g = [ inj₁ ∘ f , inj₂ ∘ g ]

infixr 1 _-⊎-_

_-⊎-_ : ∀ {a b} → (a → b → Set) → (a → b → Set) → (a → b → Set)
f -⊎- g = f -[ _⊎_ ]₁- g
