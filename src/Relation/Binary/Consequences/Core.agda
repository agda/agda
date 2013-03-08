------------------------------------------------------------------------
-- The Agda standard library
--
-- Some properties imply others
------------------------------------------------------------------------

-- This file contains some core definitions which are reexported by
-- Relation.Binary.Consequences.

module Relation.Binary.Consequences.Core where

open import Relation.Binary.Core
open import Relation.Nullary
open import Data.Product

subst⟶resp₂ : ∀ {a ℓ p} {A : Set a} {∼ : Rel A ℓ}
              (P : Rel A p) → Substitutive ∼ p → P Respects₂ ∼
subst⟶resp₂ {∼ = ∼} P subst =
  (λ {x _ _} y'∼y Pxy' → subst (P x)         y'∼y Pxy') ,
  (λ {y _ _} x'∼x Px'y → subst (λ x → P x y) x'∼x Px'y)

asym⟶irr :
  ∀ {a ℓ₁ ℓ₂} {A : Set a} {_≈_ : Rel A ℓ₁} {_<_ : Rel A ℓ₂} →
  _<_ Respects₂ _≈_ → Symmetric _≈_ →
  Asymmetric _<_ → Irreflexive _≈_ _<_
asym⟶irr {_<_ = _<_} resp sym asym {x} {y} x≈y x<y = asym x<y y<x
  where
  y<y : y < y
  y<y = proj₂ resp x≈y x<y
  y<x : y < x
  y<x = proj₁ resp (sym x≈y) y<y

tri⟶asym :
  ∀ {a ℓ₁ ℓ₂} {A : Set a} {_≈_ : Rel A ℓ₁} {_<_ : Rel A ℓ₂} →
  Trichotomous _≈_ _<_ → Asymmetric _<_
tri⟶asym tri {x} {y} x<y x>y with tri x y
... | tri< _   _ x≯y = x≯y x>y
... | tri≈ _   _ x≯y = x≯y x>y
... | tri> x≮y _ _   = x≮y x<y

tri⟶irr :
  ∀ {a ℓ₁ ℓ₂} {A : Set a} {_≈_ : Rel A ℓ₁} {_<_ : Rel A ℓ₂} →
  _<_ Respects₂ _≈_ → Symmetric _≈_ →
  Trichotomous _≈_ _<_ → Irreflexive _≈_ _<_
tri⟶irr resp sym tri = asym⟶irr resp sym (tri⟶asym tri)

tri⟶dec≈ :
  ∀ {a ℓ₁ ℓ₂} {A : Set a} {_≈_ : Rel A ℓ₁} {_<_ : Rel A ℓ₂} →
  Trichotomous _≈_ _<_ → Decidable _≈_
tri⟶dec≈ compare x y with compare x y
... | tri< _ x≉y _ = no  x≉y
... | tri≈ _ x≈y _ = yes x≈y
... | tri> _ x≉y _ = no  x≉y

tri⟶dec< :
  ∀ {a ℓ₁ ℓ₂} {A : Set a} {_≈_ : Rel A ℓ₁} {_<_ : Rel A ℓ₂} →
  Trichotomous _≈_ _<_ → Decidable _<_
tri⟶dec< compare x y with compare x y
... | tri< x<y _ _ = yes x<y
... | tri≈ x≮y _ _ = no  x≮y
... | tri> x≮y _ _ = no  x≮y
