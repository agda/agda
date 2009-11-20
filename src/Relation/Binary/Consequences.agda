------------------------------------------------------------------------
-- Some properties imply others
------------------------------------------------------------------------

{-# OPTIONS --universe-polymorphism #-}

module Relation.Binary.Consequences where

open import Relation.Binary.Core hiding (refl)
open import Relation.Nullary.Core
open import Relation.Binary.PropositionalEquality.Core
open import Data.Function
open import Data.Sum
open import Data.Product
open import Data.Empty

-- Some of the definitions can be found in the following module:

open import Relation.Binary.Consequences.Core public

trans∧irr⟶asym :
  ∀ {a ℓ₁ ℓ₂} {A : Set a} → {≈ : REL A ℓ₁} {< : REL A ℓ₂} →
  Reflexive ≈ →
  Transitive < → Irreflexive ≈ < → Asymmetric <
trans∧irr⟶asym refl trans irrefl = λ x<y y<x →
  irrefl refl (trans x<y y<x)

irr∧antisym⟶asym :
  ∀ {a ℓ₁ ℓ₂} {A : Set a} {≈ : REL A ℓ₁} {< : REL A ℓ₂} →
  Irreflexive ≈ < → Antisymmetric ≈ < → Asymmetric <
irr∧antisym⟶asym irrefl antisym = λ x<y y<x →
  irrefl (antisym x<y y<x) x<y

asym⟶antisym :
  ∀ {a ℓ₁ ℓ₂} {A : Set a} {≈ : REL A ℓ₁} {< : REL A ℓ₂} →
  Asymmetric < → Antisymmetric ≈ <
asym⟶antisym asym x<y y<x = ⊥-elim (asym x<y y<x)

asym⟶irr :
  ∀ {a ℓ₁ ℓ₂} {A : Set a} {≈ : REL A ℓ₁} {< : REL A ℓ₂} →
  < Respects₂ ≈ → Symmetric ≈ →
  Asymmetric < → Irreflexive ≈ <
asym⟶irr {< = _<_} resp sym asym {x} {y} x≈y x<y = asym x<y y<x
  where
  y<y : y < y
  y<y = proj₂ resp x≈y x<y
  y<x : y < x
  y<x = proj₁ resp (sym x≈y) y<y

total⟶refl :
  ∀ {a ℓ₁ ℓ₂} {A : Set a} {≈ : REL A ℓ₁} {∼ : REL A ℓ₂} →
  ∼ Respects₂ ≈ → Symmetric ≈ →
  Total ∼ → ≈ ⇒ ∼
total⟶refl {≈ = ≈} {∼ = ∼} resp sym total = refl
  where
  refl : ≈ ⇒ ∼
  refl {x} {y} x≈y with total x y
  ...              | inj₁ x∼y = x∼y
  ...              | inj₂ y∼x =
    proj₁ resp x≈y (proj₂ resp (sym x≈y) y∼x)

total+dec⟶dec :
  ∀ {a ℓ₁ ℓ₂} {A : Set a} {≈ : REL A ℓ₁} {≤ : REL A ℓ₂} →
  ≈ ⇒ ≤ → Antisymmetric ≈ ≤ →
  Total ≤ → Decidable ≈ → Decidable ≤
total+dec⟶dec {≈ = ≈} {≤ = ≤} refl antisym total _≟_ = dec
  where
  dec : Decidable ≤
  dec x y with total x y
  ... | inj₁ x≤y = yes x≤y
  ... | inj₂ y≤x with x ≟ y
  ...   | yes  x≈y = yes (refl x≈y)
  ...   | no  ¬x≈y = no (λ x≤y → ¬x≈y (antisym x≤y y≤x))

tri⟶asym :
  ∀ {a ℓ₁ ℓ₂} {A : Set a} {≈ : REL A ℓ₁} {< : REL A ℓ₂} →
  Trichotomous ≈ < → Asymmetric <
tri⟶asym tri {x} {y} x<y x>y with tri x y
... | tri< _   _ x≯y = x≯y x>y
... | tri≈ _   _ x≯y = x≯y x>y
... | tri> x≮y _ _   = x≮y x<y

tri⟶irr :
  ∀ {a ℓ₁ ℓ₂} {A : Set a} {≈ : REL A ℓ₁} {< : REL A ℓ₂} →
  < Respects₂ ≈ → Symmetric ≈ →
  Trichotomous ≈ < → Irreflexive ≈ <
tri⟶irr resp sym tri = asym⟶irr resp sym (tri⟶asym tri)

tri⟶dec≈ :
  ∀ {a ℓ₁ ℓ₂} {A : Set a} {≈ : REL A ℓ₁} {< : REL A ℓ₂} →
  Trichotomous ≈ < → Decidable ≈
tri⟶dec≈ compare x y with compare x y
... | tri< _ x≉y _ = no  x≉y
... | tri≈ _ x≈y _ = yes x≈y
... | tri> _ x≉y _ = no  x≉y

tri⟶dec< :
  ∀ {a ℓ₁ ℓ₂} {A : Set a} {≈ : REL A ℓ₁} {< : REL A ℓ₂} →
  Trichotomous ≈ < → Decidable <
tri⟶dec< compare x y with compare x y
... | tri< x<y _ _ = yes x<y
... | tri≈ x≮y _ _ = no  x≮y
... | tri> x≮y _ _ = no  x≮y

map-NonEmpty : ∀ {i p q} {I : Set i} {P : REL I p} {Q : REL I q} →
               P ⇒ Q → NonEmpty P → NonEmpty Q
map-NonEmpty f x = nonEmpty (f (NonEmpty.proof x))
