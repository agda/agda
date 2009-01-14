------------------------------------------------------------------------
-- Order morphisms
------------------------------------------------------------------------

module Relation.Binary.OrderMorphism where

open import Relation.Binary
open Poset
import Data.Function as F

record _⇒-Poset_ (po₁ po₂ : Poset) : Set where
  field
    fun      : carrier po₁ → carrier po₂
    monotone : _≤_ po₁ =[ fun ]⇒ _≤_ po₂

_⇒-DTO_ : (dto₁ dto₂ : DecTotalOrder) → Set
dto₁ ⇒-DTO dto₂ = poset dto₁ ⇒-Poset poset dto₂
  where open DecTotalOrder

open _⇒-Poset_

id : ∀ {po} → po ⇒-Poset po
id = record
  { fun      = F.id
  ; monotone = F.id
  }

_∘_ : ∀ {po₁ po₂ po₃} →
      po₂ ⇒-Poset po₃ → po₁ ⇒-Poset po₂ → po₁ ⇒-Poset po₃
f ∘ g = record
  { fun      = F._∘_ (fun f)      (fun g)
  ; monotone = F._∘_ (monotone f) (monotone g)
  }

const : ∀ {po₁ po₂} → carrier po₂ → po₁ ⇒-Poset po₂
const {po₂ = po₂} x = record
  { fun      = F.const x
  ; monotone = F.const (refl po₂)
  }
