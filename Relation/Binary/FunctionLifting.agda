------------------------------------------------------------------------
-- Function setoids
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
  -> Equivalence ∼₁ -> Equivalence ∼₂
  -> Equivalence (LogicalRelation ∼₁ ∼₂)
LiftEquiv {a} {b} {∼₁} {∼₂} pres eq₁ eq₂ = record
  { preorder = record
    { refl  = refl' pres
    ; trans = trans' (refl (preorder eq₁)) (trans (preorder eq₂))
    }
  ; sym = sym' (sym eq₁) (sym eq₂)
  }
  where
  open Equivalence
  open Preorder
  abstract
    refl' :  (forall f -> f Preserves ∼₁ → ∼₂)
          -> Reflexive _≡_ (LogicalRelation ∼₁ ∼₂)
    refl' pres {f} ≡-refl x∼₁y = pres f x∼₁y

    sym' :  Symmetric ∼₁
         -> Symmetric ∼₂
         -> Symmetric (LogicalRelation ∼₁ ∼₂)
    sym' sym₁ sym₂ = \f∼g x∼y -> sym₂ (f∼g (sym₁ x∼y))

    trans' :  Reflexive _≡_ ∼₁
           -> Transitive ∼₂
           -> Transitive (LogicalRelation ∼₁ ∼₂)
    trans' refl₁ trans₂ = \f∼g g∼h x∼y ->
      trans₂ (f∼g (refl₁ ≡-refl)) (g∼h x∼y)

open Setoid

LiftSetoid :  (s₁ s₂ : Setoid)
           -> (forall f -> f Preserves _≈_ s₁ → _≈_ s₂)
           -> Setoid
LiftSetoid s₁ s₂ pres = record
  { carrier = carrier s₁ -> carrier s₂
  ; _≈_     = LogicalRelation (_≈_ s₁) (_≈_ s₂)
  ; equiv   = LiftEquiv pres (equiv s₁) (equiv s₂)
  }
