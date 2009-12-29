------------------------------------------------------------------------
-- Function setoids and related constructions
------------------------------------------------------------------------

{-# OPTIONS --universe-polymorphism #-}

module Function.Equality where

open import Function as Fun using (_on_)
open import Level
open import Relation.Binary

------------------------------------------------------------------------
-- Functions which preserve equality

infixr 0 _⟶_

record _⟶_ {f₁ f₂ t₁ t₂} (From : Setoid f₁ f₂) (To : Setoid t₁ t₂) :
           Set (f₁ ⊔ f₂ ⊔ t₁ ⊔ t₂) where
  open Setoid
  infixl 5 _⟨$⟩_
  field
    _⟨$⟩_ : Carrier From → Carrier To
    cong  : _⟨$⟩_ Preserves _≈_ From ⟶ _≈_ To

open _⟶_ public

id : ∀ {a₁ a₂} {A : Setoid a₁ a₂} → A ⟶ A
id = record { _⟨$⟩_ = Fun.id; cong = Fun.id }

infixr 9 _∘_

_∘_ : ∀ {a₁ a₂} {A : Setoid a₁ a₂}
        {b₁ b₂} {B : Setoid b₁ b₂}
        {c₁ c₂} {C : Setoid c₁ c₂} →
      B ⟶ C → A ⟶ B → A ⟶ C
f ∘ g = record
  { _⟨$⟩_ = Fun._∘_ (_⟨$⟩_ f) (_⟨$⟩_ g)
  ; cong  = Fun._∘_ (cong  f) (cong  g)
  }

const : ∀ {a₁ a₂} {A : Setoid a₁ a₂}
          {b₁ b₂} {B : Setoid b₁ b₂} →
        Setoid.Carrier B → A ⟶ B
const {B = B} b = record
  { _⟨$⟩_ = Fun.const b
  ; cong  = Fun.const (Setoid.refl B)
  }

------------------------------------------------------------------------
-- A logical relation (i.e. a relation which relates functions which
-- map related things to related things)

infixr 0 _↝_

_↝_ : ∀ {a b c d ℓ₁ ℓ₂}
        {A : Set a} {B : Set b} {C : Set c} {D : Set d} →
      (∼₁ : REL A B ℓ₁) (∼₂ : REL C D ℓ₂) → REL (A → C) (B → D) _
_∼₁_ ↝ _∼₂_ = λ f g → ∀ {x y} → x ∼₁ y → f x ∼₂ g y

↝-isEquivalence : ∀ {a b c ℓ₁ ℓ₂} {A : Set a} {B : Set b} {C : Set c}
                    {∼₁ : Rel A ℓ₁} {∼₂ : Rel B ℓ₂}
                  (fun : C → (A → B)) →
                  (∀ f → fun f Preserves ∼₁ ⟶ ∼₂) →
                  IsEquivalence ∼₁ → IsEquivalence ∼₂ →
                  IsEquivalence ((∼₁ ↝ ∼₂) on fun)
↝-isEquivalence _ cong eq₁ eq₂ = record
  { refl  = λ {f} x∼₁y → cong f x∼₁y
  ; sym   = λ f∼g x∼y → sym eq₂ (f∼g (sym eq₁ x∼y))
  ; trans = λ f∼g g∼h x∼y → trans eq₂ (f∼g (refl eq₁)) (g∼h x∼y)
  } where open IsEquivalence

-- A generalised variant of (_↝_ _≡_).

≡↝ : ∀ {a b c ℓ} {A : Set a} {B : A → Set b} {C : A → Set c} →
     (∀ x → REL (B x) (C x) ℓ) →
     REL ((x : A) → B x) ((x : A) → C x) _
≡↝ R = λ f g → ∀ x → R x (f x) (g x)

≡↝-isEquivalence :
  ∀ {a b ℓ} {A : Set a} {B : A → Set b} {R : ∀ x → Rel (B x) ℓ} →
  (∀ x → IsEquivalence (R x)) → IsEquivalence (≡↝ R)
≡↝-isEquivalence eq = record
  { refl  = λ _ → refl
  ; sym   = λ f∼g x → sym (f∼g x)
  ; trans = λ f∼g g∼h x → trans (f∼g x) (g∼h x)
  } where open module Eq {x} = IsEquivalence (eq x)

------------------------------------------------------------------------
-- Function setoids

infixr 0 _⇨_ _≡⇨_

_⇨_ : ∀ {f₁ f₂ t₁ t₂} → Setoid f₁ f₂ → Setoid t₁ t₂ → Setoid _ _
S₁ ⇨ S₂ = record
  { Carrier       = S₁ ⟶ S₂
  ; _≈_           = (_≈_ S₁ ↝ _≈_ S₂) on _⟨$⟩_
  ; isEquivalence =
      ↝-isEquivalence (_⟨$⟩_ {From = S₁} {To = S₂})
                      cong (isEquivalence S₁) (isEquivalence S₂)
  } where open Setoid; open _⟶_

_≡⇨_ : ∀ {a s₁ s₂} (A : Set a) → (A → Setoid s₁ s₂) → Setoid _ _
A ≡⇨ S = record
  { Carrier       = (x : A) → Carrier (S x)
  ; _≈_           = ≡↝ (λ x → _≈_ (S x))
  ; isEquivalence = ≡↝-isEquivalence (λ x → isEquivalence (S x))
  } where open Setoid
