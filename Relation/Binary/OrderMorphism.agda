------------------------------------------------------------------------
-- Order morphisms
------------------------------------------------------------------------

module Relation.Binary.OrderMorphism where

open import Relation.Binary
open Poset
open import Data.Function

record _⇒-Poset_ (po₁ po₂ : Poset) : Set where
  field
    fun      : carrier po₁ → carrier po₂
    monotone : _≤_ po₁ =[ fun ]⇒ _≤_ po₂

_⇒-DTO_ : (dto₁ dto₂ : DecTotalOrder) → Set
dto₁ ⇒-DTO dto₂ = poset dto₁ ⇒-Poset poset dto₂
  where open DecTotalOrder

open _⇒-Poset_

idM : ∀ {po} → po ⇒-Poset po
idM = record
  { fun      = id
  ; monotone = id
  }

_∘M_ : ∀ {po₁ po₂ po₃} →
       po₂ ⇒-Poset po₃ → po₁ ⇒-Poset po₂ → po₁ ⇒-Poset po₃
f ∘M g = record
  { fun      = fun f      ∘ fun g
  ; monotone = monotone f ∘ monotone g
  }

constM : ∀ {po₁ po₂} → carrier po₂ → po₁ ⇒-Poset po₂
constM {po₂ = po₂} x = record
  { fun      = const x
  ; monotone = const (refl po₂)
  }
