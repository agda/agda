------------------------------------------------------------------------
-- Bijections
------------------------------------------------------------------------

{-# OPTIONS --universe-polymorphism #-}

module Data.Function.Bijection where

open import Data.Product
open import Level
open import Relation.Binary
open import Data.Function.Equality as F
  using (_⟶_) renaming (_∘_ to _⟪∘⟫_)
open import Data.Function.Injection  as Inj  hiding (id; _∘_)
open import Data.Function.Surjection as Surj hiding (id; _∘_)

-- Bijective functions.

record Bijective {f₁ f₂ t₁ t₂}
                 {From : Setoid f₁ f₂} {To : Setoid t₁ t₂}
                 (to : From ⟶ To) :
                 Set (f₁ ⊔ f₂ ⊔ t₁ ⊔ t₂) where
  field
    injective  : Injective  to
    surjective : Surjective to

  open Surjective surjective public

-- The set of all bijections between two setoids.

record Bijection {f₁ f₂ t₁ t₂}
                 (From : Setoid f₁ f₂) (To : Setoid t₁ t₂) :
                 Set (f₁ ⊔ f₂ ⊔ t₁ ⊔ t₂) where
  field
    to        : From ⟶ To
    bijective : Bijective to

  open Bijective bijective public

  injection : Injection From To
  injection = record
    { to        = to
    ; injective = injective
    }

  surjection : Surjection From To
  surjection = record
    { to         = to
    ; surjective = surjective
    }

  open Surjection surjection public using (right-inverse)

-- Identity and composition.

id : ∀ {s₁ s₂} {S : Setoid s₁ s₂} → Bijection S S
id {S = S} = record
  { to        = F.id
  ; bijective = record
    { injective  =  Injection.injective   (Inj.id {S = S})
    ; surjective = Surjection.surjective (Surj.id {S = S})
    }
  }

infixr 9 _∘_

_∘_ : ∀ {f₁ f₂ m₁ m₂ t₁ t₂}
        {F : Setoid f₁ f₂} {M : Setoid m₁ m₂} {T : Setoid t₁ t₂} →
      Bijection M T → Bijection F M → Bijection F T
f ∘ g = record
  { to        = to f ⟪∘⟫ to g
  ; bijective = record
    { injective  =  Injection.injective   (Inj._∘_  (injection f)  (injection g))
    ; surjective = Surjection.surjective (Surj._∘_ (surjection f) (surjection g))
    }
  } where open Bijection
