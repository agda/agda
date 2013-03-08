------------------------------------------------------------------------
-- The Agda standard library
--
-- Some properties imply others
------------------------------------------------------------------------

module Relation.Binary.Consequences where

open import Relation.Binary.Core hiding (refl)
open import Relation.Nullary
open import Relation.Nullary.Decidable as Dec
open import Relation.Binary.PropositionalEquality.Core
open import Function
open import Data.Sum
open import Data.Product
open import Data.Empty

-- Some of the definitions can be found in the following module:

open import Relation.Binary.Consequences.Core public

trans∧irr⟶asym :
  ∀ {a ℓ₁ ℓ₂} {A : Set a} → {_≈_ : Rel A ℓ₁} {_<_ : Rel A ℓ₂} →
  Reflexive _≈_ →
  Transitive _<_ → Irreflexive _≈_ _<_ → Asymmetric _<_
trans∧irr⟶asym refl trans irrefl = λ x<y y<x →
  irrefl refl (trans x<y y<x)

irr∧antisym⟶asym :
  ∀ {a ℓ₁ ℓ₂} {A : Set a} {_≈_ : Rel A ℓ₁} {_<_ : Rel A ℓ₂} →
  Irreflexive _≈_ _<_ → Antisymmetric _≈_ _<_ → Asymmetric _<_
irr∧antisym⟶asym irrefl antisym = λ x<y y<x →
  irrefl (antisym x<y y<x) x<y

asym⟶antisym :
  ∀ {a ℓ₁ ℓ₂} {A : Set a} {_≈_ : Rel A ℓ₁} {_<_ : Rel A ℓ₂} →
  Asymmetric _<_ → Antisymmetric _≈_ _<_
asym⟶antisym asym x<y y<x = ⊥-elim (asym x<y y<x)

total⟶refl :
  ∀ {a ℓ₁ ℓ₂} {A : Set a} {_≈_ : Rel A ℓ₁} {_∼_ : Rel A ℓ₂} →
  _∼_ Respects₂ _≈_ → Symmetric _≈_ →
  Total _∼_ → _≈_ ⇒ _∼_
total⟶refl {_≈_ = _≈_} {_∼_ = _∼_} resp sym total = refl
  where
  refl : _≈_ ⇒ _∼_
  refl {x} {y} x≈y with total x y
  ...              | inj₁ x∼y = x∼y
  ...              | inj₂ y∼x =
    proj₁ resp x≈y (proj₂ resp (sym x≈y) y∼x)

total+dec⟶dec :
  ∀ {a ℓ₁ ℓ₂} {A : Set a} {_≈_ : Rel A ℓ₁} {_≤_ : Rel A ℓ₂} →
  _≈_ ⇒ _≤_ → Antisymmetric _≈_ _≤_ →
  Total _≤_ → Decidable _≈_ → Decidable _≤_
total+dec⟶dec {_≈_ = _≈_} {_≤_ = _≤_} refl antisym total _≟_ = dec
  where
  dec : Decidable _≤_
  dec x y with total x y
  ... | inj₁ x≤y = yes x≤y
  ... | inj₂ y≤x with x ≟ y
  ...   | yes  x≈y = yes (refl x≈y)
  ...   | no  ¬x≈y = no (λ x≤y → ¬x≈y (antisym x≤y y≤x))

map-NonEmpty : ∀ {a b p q} {A : Set a} {B : Set b}
                 {P : REL A B p} {Q : REL A B q} →
               P ⇒ Q → NonEmpty P → NonEmpty Q
map-NonEmpty f x = nonEmpty (f (NonEmpty.proof x))

map-Decidable : ∀ {a b p q} {A : Set a} {B : Set b}
                  {P : REL A B p} {Q : REL A B q} →
                P ⇒ Q → Q ⇒ P → Decidable P → Decidable Q
map-Decidable to from dec x y = Dec.map′ to from (dec x y)
