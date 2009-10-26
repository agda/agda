------------------------------------------------------------------------
-- Propositional equality
------------------------------------------------------------------------

{-# OPTIONS --universe-polymorphism #-}

-- This file contains some core definitions which are reexported by
-- Relation.Binary.PropositionalEquality.

module Relation.Binary.PropositionalEquality.Core where

open import Level
open import Relation.Binary.Core
open import Relation.Binary.Consequences.Core

------------------------------------------------------------------------
-- Some properties

sym : ∀ {a} {A : Set a} {x y : A} → x ≡ y → y ≡ x
sym refl = refl

trans : ∀ {a} {A : Set a} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
trans refl refl = refl

subst : ∀ {a p} {A : Set a} (P : A → Set p) {x y} → x ≡ y → P x → P y
subst P refl p = p

resp₂ : ∀ {a} (∼ : Rel a) → ∼ Respects₂ _≡_
resp₂ _∼_ = subst⟶resp₂ _∼_ subst

isEquivalence : ∀ {a} → IsEquivalence {a} _≡_
isEquivalence = record
  { refl  = refl
  ; sym   = sym
  ; trans = trans
  }
