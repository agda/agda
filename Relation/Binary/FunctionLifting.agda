------------------------------------------------------------------------
-- (Some) function setoids
------------------------------------------------------------------------

module Relation.Binary.FunctionLifting where

open import Relation.Binary

_↝_ : forall {a b} -> (∼₁ : Rel a) (∼₂ : Rel b) -> Rel (a -> b)
_∼₁_ ↝ _∼₂_ = \f g -> forall {x y} -> x ∼₁ y -> f x ∼₂ g y

LiftEquiv
  :  forall {a b} {∼₁ : Rel a} {∼₂ : Rel b}
  -> (forall f -> f Preserves ∼₁ → ∼₂)
  -> IsEquivalence ∼₁ -> IsEquivalence ∼₂
  -> IsEquivalence (∼₁ ↝ ∼₂)
LiftEquiv {a} {b} {∼₁} {∼₂} pres eq₁ eq₂ = record
  { refl  = \{f} -> refl' {f}
  ; sym   = sym' (sym eq₁) (sym eq₂)
  ; trans = trans' (refl eq₁) (trans eq₂)
  }
  where
  open IsEquivalence

  refl' : Reflexive (∼₁ ↝ ∼₂)
  refl' {f} x∼₁y = pres f x∼₁y

  sym' :  Symmetric ∼₁
       -> Symmetric ∼₂
       -> Symmetric (∼₁ ↝ ∼₂)
  sym' sym₁ sym₂ = \f∼g x∼y -> sym₂ (f∼g (sym₁ x∼y))

  trans' :  Reflexive ∼₁
         -> Transitive ∼₂
         -> Transitive (∼₁ ↝ ∼₂)
  trans' refl₁ trans₂ = \f∼g g∼h x∼y ->
    trans₂ (f∼g refl₁) (g∼h x∼y)

LiftSetoid :  (s₁ s₂ : Setoid)
           -> (forall f -> f Preserves Setoid._≈_ s₁ → Setoid._≈_ s₂)
           -> Setoid
LiftSetoid s₁ s₂ pres = record
  { carrier       = carrier s₁ -> carrier s₂
  ; _≈_           = _≈_ s₁ ↝ _≈_ s₂
  ; isEquivalence = LiftEquiv pres (isEquivalence s₁) (isEquivalence s₂)
  }
  where open Setoid

≡↝ : {a b : Set} -> Rel b -> Rel (a -> b)
≡↝ _∼_ = \f g -> forall x -> f x ∼ g x

LiftEquiv≡
  :  forall {a b} {∼ : Rel b}
  -> IsEquivalence ∼ -> IsEquivalence (≡↝ {a} ∼)
LiftEquiv≡ {a} {b} {∼} eq = record
  { refl  = \_ -> refl
  ; sym   = \f∼g x -> sym (f∼g x)
  ; trans = \f∼g g∼h x -> trans (f∼g x) (g∼h x)
  }
  where open IsEquivalence eq

LiftSetoid≡ : Set -> Setoid -> Setoid
LiftSetoid≡ a₁ s₂ = record
  { carrier       = a₁ -> carrier s₂
  ; _≈_           = ≡↝ (_≈_ s₂)
  ; isEquivalence = LiftEquiv≡ (isEquivalence s₂)
  }
  where open Setoid
