------------------------------------------------------------------------
-- (Some) function setoids
------------------------------------------------------------------------

module Relation.Binary.FunctionLifting where

open import Relation.Binary

_↝_ : ∀ {a b} → (∼₁ : Rel a) (∼₂ : Rel b) → Rel (a → b)
_∼₁_ ↝ _∼₂_ = λ f g → ∀ {x y} → x ∼₁ y → f x ∼₂ g y

LiftEquiv : ∀ {a b} {∼₁ : Rel a} {∼₂ : Rel b} →
            (∀ f → f Preserves ∼₁ ⟶ ∼₂) →
            IsEquivalence ∼₁ → IsEquivalence ∼₂ →
            IsEquivalence (∼₁ ↝ ∼₂)
LiftEquiv {a} {b} {∼₁} {∼₂} pres eq₁ eq₂ = record
  { refl  = λ {f} → refl' {f}
  ; sym   = sym' (sym eq₁) (sym eq₂)
  ; trans = trans' (refl eq₁) (trans eq₂)
  }
  where
  open IsEquivalence

  refl' : Reflexive (∼₁ ↝ ∼₂)
  refl' {f} x∼₁y = pres f x∼₁y

  sym' : Symmetric ∼₁ →
         Symmetric ∼₂ →
         Symmetric (∼₁ ↝ ∼₂)
  sym' sym₁ sym₂ = λ f∼g x∼y → sym₂ (f∼g (sym₁ x∼y))

  trans' : Reflexive ∼₁ →
           Transitive ∼₂ →
           Transitive (∼₁ ↝ ∼₂)
  trans' refl₁ trans₂ = λ f∼g g∼h x∼y →
    trans₂ (f∼g refl₁) (g∼h x∼y)

LiftSetoid : (s₁ s₂ : Setoid) →
             (∀ f → f Preserves Setoid._≈_ s₁ ⟶ Setoid._≈_ s₂) →
             Setoid
LiftSetoid s₁ s₂ pres = record
  { carrier       = carrier s₁ → carrier s₂
  ; _≈_           = _≈_ s₁ ↝ _≈_ s₂
  ; isEquivalence = LiftEquiv pres (isEquivalence s₁) (isEquivalence s₂)
  }
  where open Setoid

≡↝ : ∀ {A} {B : A → Set} → (∀ x → Rel (B x)) → Rel ((x : A) → B x)
≡↝ R = λ f g → ∀ x → R x (f x) (g x)

LiftEquiv≡ : {A : Set} {B : A → Set} {R : ∀ x → Rel (B x)} →
             (∀ x → IsEquivalence (R x)) → IsEquivalence (≡↝ R)
LiftEquiv≡ eq = record
  { refl  = λ _ → refl
  ; sym   = λ f∼g x → sym (f∼g x)
  ; trans = λ f∼g g∼h x → trans (f∼g x) (g∼h x)
  }
  where open module Eq {x} = IsEquivalence (eq x)

LiftSetoid≡ : (A : Set) → (A → Setoid) → Setoid
LiftSetoid≡ A S = record
  { carrier       = (x : A) → carrier (S x)
  ; _≈_           = ≡↝ (λ x → _≈_ (S x))
  ; isEquivalence = LiftEquiv≡ (λ x → isEquivalence (S x))
  }
  where open Setoid
