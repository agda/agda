------------------------------------------------------------------------
-- The Agda standard library
--
-- Order morphisms
------------------------------------------------------------------------

module Relation.Binary.OrderMorphism where

open import Relation.Binary
open Poset
import Function as F
open import Level

record _⇒-Poset_ {p₁ p₂ p₃ p₄ p₅ p₆}
                 (P₁ : Poset p₁ p₂ p₃)
                 (P₂ : Poset p₄ p₅ p₆) : Set (p₁ ⊔ p₃ ⊔ p₄ ⊔ p₆) where
  field
    fun      : Carrier P₁ → Carrier P₂
    monotone : _≤_ P₁ =[ fun ]⇒ _≤_ P₂

_⇒-DTO_ : ∀ {p₁ p₂ p₃ p₄ p₅ p₆} →
          DecTotalOrder p₁ p₂ p₃ →
          DecTotalOrder p₄ p₅ p₆ → Set _
DTO₁ ⇒-DTO DTO₂ = poset DTO₁ ⇒-Poset poset DTO₂
  where open DecTotalOrder

open _⇒-Poset_

id : ∀ {p₁ p₂ p₃} {P : Poset p₁ p₂ p₃} → P ⇒-Poset P
id = record
  { fun      = F.id
  ; monotone = F.id
  }

_∘_ : ∀ {p₁ p₂ p₃ p₄ p₅ p₆ p₇ p₈ p₉}
        {P₁ : Poset p₁ p₂ p₃}
        {P₂ : Poset p₄ p₅ p₆}
        {P₃ : Poset p₇ p₈ p₉} →
      P₂ ⇒-Poset P₃ → P₁ ⇒-Poset P₂ → P₁ ⇒-Poset P₃
f ∘ g = record
  { fun      = F._∘_ (fun f)      (fun g)
  ; monotone = F._∘_ (monotone f) (monotone g)
  }

const : ∀ {p₁ p₂ p₃ p₄ p₅ p₆}
          {P₁ : Poset p₁ p₂ p₃}
          {P₂ : Poset p₄ p₅ p₆} →
        Carrier P₂ → P₁ ⇒-Poset P₂
const {P₂ = P₂} x = record
  { fun      = F.const x
  ; monotone = F.const (refl P₂)
  }
