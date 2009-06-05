------------------------------------------------------------------------
-- Sums (disjoint unions)
------------------------------------------------------------------------

module Data.Sum where

open import Data.Function
open import Data.Maybe.Core

------------------------------------------------------------------------
-- Definition

infixr 1 _⊎_

data _⊎_ (A B : Set) : Set where
  inj₁ : (x : A) → A ⊎ B
  inj₂ : (y : B) → A ⊎ B

------------------------------------------------------------------------
-- Functions

[_,_] : ∀ {A B} {C : A ⊎ B → Set} →
        ((x : A) → C (inj₁ x)) → ((x : B) → C (inj₂ x)) →
        ((x : A ⊎ B) → C x)
[ f , g ] (inj₁ x) = f x
[ f , g ] (inj₂ y) = g y

[_,_]′ : ∀ {A B C : Set} → (A → C) → (B → C) → (A ⊎ B → C)
[_,_]′ = [_,_]

map : ∀ {a b c d} → (a → c) → (b → d) → (a ⊎ b → c ⊎ d)
map f g = [ inj₁ ∘ f , inj₂ ∘ g ]

infixr 1 _-⊎-_

_-⊎-_ : ∀ {a b} → (a → b → Set) → (a → b → Set) → (a → b → Set)
f -⊎- g = f -[ _⊎_ ]₁- g

isInj₁ : ∀ {A B} → A ⊎ B → Maybe A
isInj₁ (inj₁ x) = just x
isInj₁ (inj₂ y) = nothing

isInj₂ : ∀ {A B} → A ⊎ B → Maybe B
isInj₂ (inj₁ x) = nothing
isInj₂ (inj₂ y) = just y
