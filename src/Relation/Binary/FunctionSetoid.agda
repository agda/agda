------------------------------------------------------------------------
-- Function setoids and related constructions
------------------------------------------------------------------------

module Relation.Binary.FunctionSetoid where

open import Data.Function
open import Relation.Binary

infixr 0 _↝_ _⟶_ _⇨_ _≡⇨_

-- A logical relation (i.e. a relation which relates functions which
-- map related things to related things).

_↝_ : ∀ {A B} → (∼₁ : Rel A) (∼₂ : Rel B) → Rel (A → B)
_∼₁_ ↝ _∼₂_ = λ f g → ∀ {x y} → x ∼₁ y → f x ∼₂ g y

-- Functions which preserve equality.

record _⟶_ (From To : Setoid) : Set where
  open Setoid
  infixl 5 _⟨$⟩_
  field
    _⟨$⟩_ : carrier From → carrier To
    pres  : _⟨$⟩_ Preserves _≈_ From ⟶ _≈_ To

open _⟶_ public

↝-isEquivalence : ∀ {A B C} {∼₁ : Rel A} {∼₂ : Rel B}
                  (fun : C → (A → B)) →
                  (∀ f → fun f Preserves ∼₁ ⟶ ∼₂) →
                  IsEquivalence ∼₁ → IsEquivalence ∼₂ →
                  IsEquivalence ((∼₁ ↝ ∼₂) on₁ fun)
↝-isEquivalence _ pres eq₁ eq₂ = record
  { refl  = λ {f} x∼₁y → pres f x∼₁y
  ; sym   = λ f∼g x∼y → sym eq₂ (f∼g (sym eq₁ x∼y))
  ; trans = λ f∼g g∼h x∼y → trans eq₂ (f∼g (refl eq₁)) (g∼h x∼y)
  } where open IsEquivalence

-- Function setoids.

_⇨_ : Setoid → Setoid → Setoid
S₁ ⇨ S₂ = record
  { carrier       = S₁ ⟶ S₂
  ; _≈_           = (_≈_ S₁ ↝ _≈_ S₂) on₁ _⟨$⟩_
  ; isEquivalence =
      ↝-isEquivalence _⟨$⟩_ pres (isEquivalence S₁) (isEquivalence S₂)
  } where open Setoid; open _⟶_

-- A generalised variant of (_↝_ _≡_).

≡↝ : ∀ {A} {B : A → Set} → (∀ x → Rel (B x)) → Rel ((x : A) → B x)
≡↝ R = λ f g → ∀ x → R x (f x) (g x)

≡↝-isEquivalence : {A : Set} {B : A → Set} {R : ∀ x → Rel (B x)} →
                   (∀ x → IsEquivalence (R x)) → IsEquivalence (≡↝ R)
≡↝-isEquivalence eq = record
  { refl  = λ _ → refl
  ; sym   = λ f∼g x → sym (f∼g x)
  ; trans = λ f∼g g∼h x → trans (f∼g x) (g∼h x)
  } where open module Eq {x} = IsEquivalence (eq x)

_≡⇨_ : (A : Set) → (A → Setoid) → Setoid
A ≡⇨ S = record
  { carrier       = (x : A) → carrier (S x)
  ; _≈_           = ≡↝ (λ x → _≈_ (S x))
  ; isEquivalence = ≡↝-isEquivalence (λ x → isEquivalence (S x))
  } where open Setoid
