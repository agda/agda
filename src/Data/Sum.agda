------------------------------------------------------------------------
-- The Agda standard library
--
-- Sums (disjoint unions)
------------------------------------------------------------------------

module Data.Sum where

open import Function
open import Data.Maybe.Minimal using (Maybe; just; nothing)
open import Level

------------------------------------------------------------------------
-- Definition

infixr 1 _⊎_

data _⊎_ {a b} (A : Set a) (B : Set b) : Set (a ⊔ b) where
  inj₁ : (x : A) → A ⊎ B
  inj₂ : (y : B) → A ⊎ B

{-# IMPORT Data.FFI #-}
{-# COMPILED_DATA _⊎_ Data.FFI.AgdaEither Left Right #-}

------------------------------------------------------------------------
-- Functions

[_,_] : ∀ {a b c} {A : Set a} {B : Set b} {C : A ⊎ B → Set c} →
        ((x : A) → C (inj₁ x)) → ((x : B) → C (inj₂ x)) →
        ((x : A ⊎ B) → C x)
[ f , g ] (inj₁ x) = f x
[ f , g ] (inj₂ y) = g y

[_,_]′ : ∀ {a b c} {A : Set a} {B : Set b} {C : Set c} →
         (A → C) → (B → C) → (A ⊎ B → C)
[_,_]′ = [_,_]

map : ∀ {a b c d} {A : Set a} {B : Set b} {C : Set c} {D : Set d} →
      (A → C) → (B → D) → (A ⊎ B → C ⊎ D)
map f g = [ inj₁ ∘ f , inj₂ ∘ g ]

infixr 1 _-⊎-_

_-⊎-_ : ∀ {a b c d} {A : Set a} {B : Set b} →
        (A → B → Set c) → (A → B → Set d) → (A → B → Set (c ⊔ d))
f -⊎- g = f -[ _⊎_ ]- g

isInj₁ : ∀ {a b} {A : Set a} {B : Set b} → A ⊎ B → Maybe A
isInj₁ (inj₁ x) = just x
isInj₁ (inj₂ y) = nothing

isInj₂ : ∀ {a b} {A : Set a} {B : Set b} → A ⊎ B → Maybe B
isInj₂ (inj₁ x) = nothing
isInj₂ (inj₂ y) = just y
