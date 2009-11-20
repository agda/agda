------------------------------------------------------------------------
-- Function setoids and related constructions
------------------------------------------------------------------------

{-# OPTIONS --universe-polymorphism #-}

module Relation.Binary.FunctionSetoid where

open import Data.Function
open import Level
open import Relation.Binary

infixr 0 _↝_ _⟶_ _⇨_ _≡⇨_

-- A logical relation (i.e. a relation which relates functions which
-- map related things to related things).

_↝_ : ∀ {a b ℓ₁ ℓ₂} {A : Set a} {B : Set b} →
      (∼₁ : REL A ℓ₁) (∼₂ : REL B ℓ₂) → REL (A → B) (a ⊔ ℓ₁ ⊔ ℓ₂)
_∼₁_ ↝ _∼₂_ = λ f g → ∀ {x y} → x ∼₁ y → f x ∼₂ g y

-- Functions which preserve equality.

record _⟶_ {f₁ f₂ t₁ t₂} (From : Setoid f₁ f₂) (To : Setoid t₁ t₂) :
           Set (f₁ ⊔ f₂ ⊔ t₁ ⊔ t₂) where
  open Setoid
  infixl 5 _⟨$⟩_
  field
    _⟨$⟩_ : Carrier From → Carrier To
    pres  : _⟨$⟩_ Preserves _≈_ From ⟶ _≈_ To

open _⟶_ public

↝-isEquivalence : ∀ {a b c ℓ₁ ℓ₂} {A : Set a} {B : Set b} {C : Set c}
                    {∼₁ : REL A ℓ₁} {∼₂ : REL B ℓ₂}
                  (fun : C → (A → B)) →
                  (∀ f → fun f Preserves ∼₁ ⟶ ∼₂) →
                  IsEquivalence ∼₁ → IsEquivalence ∼₂ →
                  IsEquivalence ((∼₁ ↝ ∼₂) on fun)
↝-isEquivalence _ pres eq₁ eq₂ = record
  { refl  = λ {f} x∼₁y → pres f x∼₁y
  ; sym   = λ f∼g x∼y → sym eq₂ (f∼g (sym eq₁ x∼y))
  ; trans = λ f∼g g∼h x∼y → trans eq₂ (f∼g (refl eq₁)) (g∼h x∼y)
  } where open IsEquivalence

-- Function setoids.

_⇨_ : ∀ {f₁ f₂ t₁ t₂} → Setoid f₁ f₂ → Setoid t₁ t₂ → Setoid _ _
S₁ ⇨ S₂ = record
  { Carrier       = S₁ ⟶ S₂
  ; _≈_           = (_≈_ S₁ ↝ _≈_ S₂) on _⟨$⟩_
  ; isEquivalence =
      ↝-isEquivalence (_⟨$⟩_ {From = S₁} {To = S₂})
                      pres (isEquivalence S₁) (isEquivalence S₂)
  } where open Setoid; open _⟶_

-- A generalised variant of (_↝_ _≡_).

≡↝ : ∀ {a b ℓ} {A : Set a} {B : A → Set b} →
     (∀ x → REL (B x) ℓ) → REL ((x : A) → B x) _
≡↝ R = λ f g → ∀ x → R x (f x) (g x)

≡↝-isEquivalence :
  ∀ {a b ℓ} {A : Set a} {B : A → Set b} {R : ∀ x → REL (B x) ℓ} →
  (∀ x → IsEquivalence (R x)) → IsEquivalence (≡↝ R)
≡↝-isEquivalence eq = record
  { refl  = λ _ → refl
  ; sym   = λ f∼g x → sym (f∼g x)
  ; trans = λ f∼g g∼h x → trans (f∼g x) (g∼h x)
  } where open module Eq {x} = IsEquivalence (eq x)

_≡⇨_ : ∀ {a s₁ s₂} (A : Set a) → (A → Setoid s₁ s₂) → Setoid _ _
A ≡⇨ S = record
  { Carrier       = (x : A) → Carrier (S x)
  ; _≈_           = ≡↝ (λ x → _≈_ (S x))
  ; isEquivalence = ≡↝-isEquivalence (λ x → isEquivalence (S x))
  } where open Setoid
