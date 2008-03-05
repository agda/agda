------------------------------------------------------------------------
-- (Some) function setoids
------------------------------------------------------------------------

module Relation.Binary.FunctionLifting where

open import Logic
open import Relation.Binary

LogicalRelation
  :  forall {a b}
  -> (∼₁ : Rel a) (∼₂ : Rel b) -> Rel (a -> b)
LogicalRelation _∼₁_ _∼₂_ =
  \f g -> forall {x y} -> x ∼₁ y -> f x ∼₂ g y

LiftEquiv
  :  forall {a b} {∼₁ : Rel a} {∼₂ : Rel b}
  -> (forall f -> f Preserves ∼₁ → ∼₂)
  -> IsEquivalence ∼₁ -> IsEquivalence ∼₂
  -> IsEquivalence (LogicalRelation ∼₁ ∼₂)
LiftEquiv {a} {b} {∼₁} {∼₂} pres eq₁ eq₂ = record
  { refl  = \{f} -> refl' {f}
  ; sym   = sym' (sym eq₁) (sym eq₂)
  ; trans = trans' (refl eq₁) (trans eq₂)
  }
  where
  open IsEquivalence

  refl' : Refl (LogicalRelation ∼₁ ∼₂)
  refl' {f} x∼₁y = pres f x∼₁y

  sym' :  Symmetric ∼₁
       -> Symmetric ∼₂
       -> Symmetric (LogicalRelation ∼₁ ∼₂)
  sym' sym₁ sym₂ = \f∼g x∼y -> sym₂ (f∼g (sym₁ x∼y))

  trans' :  Refl ∼₁
         -> Transitive ∼₂
         -> Transitive (LogicalRelation ∼₁ ∼₂)
  trans' refl₁ trans₂ = \f∼g g∼h x∼y ->
    trans₂ (f∼g refl₁) (g∼h x∼y)

open Setoid

LiftSetoid :  (s₁ s₂ : Setoid)
           -> (forall f -> f Preserves _≈_ s₁ → _≈_ s₂)
           -> Setoid
LiftSetoid s₁ s₂ pres = record
  { carrier       = carrier s₁ -> carrier s₂
  ; _≈_           = LogicalRelation (_≈_ s₁) (_≈_ s₂)
  ; isEquivalence = LiftEquiv pres (isEquivalence s₁) (isEquivalence s₂)
  }
