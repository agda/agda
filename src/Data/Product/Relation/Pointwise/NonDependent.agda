------------------------------------------------------------------------
-- The Agda standard library
--
-- Pointwise products of binary relations
------------------------------------------------------------------------

module Data.Product.Relation.Pointwise.NonDependent where

open import Data.Product as Prod
import Data.Product.Relation.Pointwise.Dependent as Dependent
open import Data.Sum
open import Data.Unit.Base using (⊤)
open import Function
open import Function.Equality as F using (_⟶_; _⟨$⟩_)
open import Function.Equivalence as Eq
  using (Equivalence; _⇔_; module Equivalence)
open import Function.Injection as Inj
  using (Injection; _↣_; module Injection)
open import Function.Inverse as Inv
  using (Inverse; _↔_; module Inverse)
open import Function.LeftInverse as LeftInv
  using (LeftInverse; _↞_; _LeftInverseOf_; module LeftInverse)
open import Function.Related
open import Function.Surjection as Surj
  using (Surjection; _↠_; module Surjection)
import Relation.Nullary.Decidable as Dec
open import Relation.Nullary.Product
open import Relation.Binary
open import Relation.Binary.PropositionalEquality as P using (_≡_)

module _ {a₁ a₂ ℓ₁ ℓ₂} {A₁ : Set a₁} {A₂ : Set a₂} where

------------------------------------------------------------------------
-- Pointwise lifting

  Pointwise : Rel A₁ ℓ₁ → Rel A₂ ℓ₂ → Rel (A₁ × A₂) _
  Pointwise _∼₁_ _∼₂_ = (_∼₁_ on proj₁) -×- (_∼₂_ on proj₂)

------------------------------------------------------------------------
-- Pointwise preserves many relational properties

  ×-reflexive : ∀ {_≈₁_ _∼₁_ _≈₂_ _∼₂_} →
    _≈₁_ ⇒ _∼₁_ → _≈₂_ ⇒ _∼₂_ →
    (Pointwise _≈₁_ _≈₂_) ⇒ (Pointwise _∼₁_ _∼₂_)
  ×-reflexive refl₁ refl₂ (x∼y₁ , x∼y₂) = refl₁ x∼y₁ , refl₂ x∼y₂

  ×-refl : ∀ {_∼₁_ _∼₂_} →
    Reflexive _∼₁_ → Reflexive _∼₂_ →
    Reflexive (Pointwise _∼₁_ _∼₂_)
  ×-refl refl₁ refl₂ = refl₁ , refl₂

  ×-irreflexive₁ : ∀ {_≈₁_ _<₁_ _≈₂_ _<₂_} →
    Irreflexive _≈₁_ _<₁_ →
    Irreflexive (Pointwise _≈₁_ _≈₂_) (Pointwise _<₁_ _<₂_)
  ×-irreflexive₁ ir x≈y x<y = ir (proj₁ x≈y) (proj₁ x<y)

  ×-irreflexive₂ : ∀ {_≈₁_ _<₁_ _≈₂_ _<₂_} →
    Irreflexive _≈₂_ _<₂_ →
    Irreflexive (Pointwise _≈₁_ _≈₂_) (Pointwise _<₁_ _<₂_)
  ×-irreflexive₂ ir x≈y x<y = ir (proj₂ x≈y) (proj₂ x<y)

  ×-symmetric : ∀ {_∼₁_ _∼₂_} → Symmetric _∼₁_ → Symmetric _∼₂_ →
    Symmetric (Pointwise _∼₁_ _∼₂_)
  ×-symmetric sym₁ sym₂ (x∼y₁ , x∼y₂) = sym₁ x∼y₁ , sym₂ x∼y₂

  ×-transitive : ∀ {_∼₁_ _∼₂_} → Transitive _∼₁_ → Transitive _∼₂_ →
    Transitive (Pointwise _∼₁_ _∼₂_)
  ×-transitive trans₁ trans₂ x∼y y∼z =
    trans₁ (proj₁ x∼y) (proj₁ y∼z) ,
    trans₂ (proj₂ x∼y) (proj₂ y∼z)

  ×-antisymmetric : ∀ {_≈₁_ _≤₁_ _≈₂_ _≤₂_} →
    Antisymmetric _≈₁_ _≤₁_ → Antisymmetric _≈₂_ _≤₂_ →
    Antisymmetric (Pointwise _≈₁_ _≈₂_) (Pointwise _≤₁_ _≤₂_)
  ×-antisymmetric antisym₁ antisym₂ (x≤y₁ , x≤y₂) (y≤x₁ , y≤x₂) =
    (antisym₁ x≤y₁ y≤x₁ , antisym₂ x≤y₂ y≤x₂)

  ×-asymmetric₁ : ∀ {_<₁_ _∼₂_} → Asymmetric _<₁_ →
    Asymmetric (Pointwise _<₁_ _∼₂_)
  ×-asymmetric₁ asym₁ x<y y<x = asym₁ (proj₁ x<y) (proj₁ y<x)

  ×-asymmetric₂ : ∀ {_∼₁_ _<₂_} → Asymmetric _<₂_ →
    Asymmetric (Pointwise _∼₁_ _<₂_)
  ×-asymmetric₂ asym₂ x<y y<x = asym₂ (proj₂ x<y) (proj₂ y<x)

  ×-respects₂ : ∀ {_≈₁_ _∼₁_ _≈₂_ _∼₂_} →
    _∼₁_ Respects₂ _≈₁_ → _∼₂_ Respects₂ _≈₂_ →
    (Pointwise _∼₁_ _∼₂_) Respects₂ (Pointwise _≈₁_ _≈₂_)
  ×-respects₂ {_≈₁_} {_∼₁_} {_≈₂_} {_∼₂_} resp₁ resp₂ = resp¹ , resp²
    where
    _∼_ = Pointwise _∼₁_ _∼₂_
    _≈_ = Pointwise _≈₁_ _≈₂_

    resp¹ : ∀ {x} → (x ∼_) Respects _≈_
    resp¹ y≈y' x∼y = proj₁ resp₁ (proj₁ y≈y') (proj₁ x∼y) ,
                     proj₁ resp₂ (proj₂ y≈y') (proj₂ x∼y)

    resp² : ∀ {y} → (_∼ y) Respects _≈_
    resp² x≈x' x∼y = proj₂ resp₁ (proj₁ x≈x') (proj₁ x∼y) ,
                     proj₂ resp₂ (proj₂ x≈x') (proj₂ x∼y)

  ×-total : ∀ {_∼₁_ _∼₂_} → Symmetric _∼₁_ →
    Total _∼₁_ → Total _∼₂_ →
    Total (Pointwise _∼₁_ _∼₂_)
  ×-total sym₁ total₁ total₂ (x₁ , x₂) (y₁ , y₂)
    with total₁ x₁ y₁ | total₂ x₂ y₂
  ... | inj₁ x₁∼y₁ | inj₁ x₂∼y₂ = inj₁ (     x₁∼y₁ , x₂∼y₂)
  ... | inj₁ x₁∼y₁ | inj₂ y₂∼x₂ = inj₂ (sym₁ x₁∼y₁ , y₂∼x₂)
  ... | inj₂ y₁∼x₁ | inj₂ y₂∼x₂ = inj₂ (     y₁∼x₁ , y₂∼x₂)
  ... | inj₂ y₁∼x₁ | inj₁ x₂∼y₂ = inj₁ (sym₁ y₁∼x₁ , x₂∼y₂)

  ×-decidable : ∀ {_∼₁_ _∼₂_} →
    Decidable _∼₁_ → Decidable _∼₂_ →
    Decidable (Pointwise _∼₁_ _∼₂_)
  ×-decidable _≟₁_ _≟₂_ (x₁ , x₂) (y₁ , y₂) =
    (x₁ ≟₁ y₁) ×-dec (x₂ ≟₂ y₂)

  -- Some collections of properties which are preserved by ×-Rel.

  ×-isEquivalence : ∀ {_≈₁_ _≈₂_} →
    IsEquivalence _≈₁_ → IsEquivalence _≈₂_ →
    IsEquivalence (Pointwise _≈₁_ _≈₂_)
  ×-isEquivalence {_≈₁_ = _≈₁_} {_≈₂_ = _≈₂_} eq₁ eq₂ = record
    { refl  = ×-refl        {_∼₁_ = _≈₁_} {_∼₂_ = _≈₂_}
                            (refl  eq₁) (refl  eq₂)
    ; sym   = ×-symmetric   {_∼₁_ = _≈₁_} {_∼₂_ = _≈₂_}
                            (sym   eq₁) (sym   eq₂)
    ; trans = ×-transitive  {_∼₁_ = _≈₁_} {_∼₂_ = _≈₂_}
                            (trans eq₁) (trans eq₂)
    }
    where open IsEquivalence

  ×-isDecEquivalence : ∀ {_≈₁_ _≈₂_} →
    IsDecEquivalence _≈₁_ → IsDecEquivalence _≈₂_ →
    IsDecEquivalence (Pointwise _≈₁_ _≈₂_)
  ×-isDecEquivalence eq₁ eq₂ = record
    { isEquivalence = ×-isEquivalence
                        (isEquivalence eq₁) (isEquivalence eq₂)
    ; _≟_           = ×-decidable (_≟_ eq₁) (_≟_ eq₂)
    }
    where open IsDecEquivalence

  ×-isPreorder : ∀ {_≈₁_ _∼₁_ _≈₂_ _∼₂_} →
    IsPreorder _≈₁_ _∼₁_ → IsPreorder _≈₂_ _∼₂_ →
    IsPreorder (Pointwise _≈₁_ _≈₂_) (Pointwise _∼₁_ _∼₂_)
  ×-isPreorder {_∼₁_ = _∼₁_} {_∼₂_ = _∼₂_} pre₁ pre₂ = record
    { isEquivalence = ×-isEquivalence
                        (isEquivalence pre₁) (isEquivalence pre₂)
    ; reflexive     = ×-reflexive {_∼₁_ = _∼₁_} {_∼₂_ = _∼₂_}
                        (reflexive pre₁) (reflexive pre₂)
    ; trans         = ×-transitive {_∼₁_ = _∼₁_} {_∼₂_ = _∼₂_}
                        (trans pre₁) (trans pre₂)
    }
    where open IsPreorder

  ×-isPartialOrder : ∀ {_≈₁_ _≤₁_ _≈₂_ _≤₂_} →
    IsPartialOrder _≈₁_ _≤₁_ → IsPartialOrder _≈₂_ _≤₂_ →
    IsPartialOrder (Pointwise _≈₁_ _≈₂_) (Pointwise _≤₁_ _≤₂_)
  ×-isPartialOrder {_≤₁_ = _≤₁_} {_≤₂_ = _≤₂_} po₁ po₂ = record
    { isPreorder = ×-isPreorder (isPreorder po₁) (isPreorder po₂)
    ; antisym    = ×-antisymmetric {_≤₁_ = _≤₁_} {_≤₂_ = _≤₂_}
                     (antisym po₁) (antisym po₂)
    }
    where open IsPartialOrder

  ×-isStrictPartialOrder : ∀ {_≈₁_ _<₁_ _≈₂_ _<₂_} →
    IsStrictPartialOrder _≈₁_ _<₁_ → IsStrictPartialOrder _≈₂_ _<₂_ →
    IsStrictPartialOrder (Pointwise _≈₁_ _≈₂_) (Pointwise _<₁_ _<₂_)
  ×-isStrictPartialOrder {_<₁_ = _<₁_} {_≈₂_ = _≈₂_} {_<₂_ = _<₂_}
                           spo₁ spo₂ =
    record
      { isEquivalence = ×-isEquivalence
                          (isEquivalence spo₁) (isEquivalence spo₂)
      ; irrefl        = ×-irreflexive₁ {_<₁_ = _<₁_} {_≈₂_} {_<₂_}
                          (irrefl spo₁)
      ; trans         = ×-transitive {_∼₁_ = _<₁_} {_<₂_}
                          (trans spo₁) (trans spo₂)
      ; <-resp-≈      = ×-respects₂ (<-resp-≈ spo₁) (<-resp-≈ spo₂)
      }
    where open IsStrictPartialOrder

------------------------------------------------------------------------
-- "Packages" can also be combined.

module _ {ℓ₁ ℓ₂ ℓ₃ ℓ₄} where

  ×-preorder : Preorder ℓ₁ ℓ₂ _ → Preorder ℓ₃ ℓ₄ _ → Preorder _ _ _
  ×-preorder p₁ p₂ = record
    { isPreorder = ×-isPreorder (isPreorder p₁) (isPreorder p₂)
    } where open Preorder

  ×-setoid : Setoid ℓ₁ ℓ₂ → Setoid ℓ₃ ℓ₄ → Setoid _ _
  ×-setoid s₁ s₂ = record
    { isEquivalence =
        ×-isEquivalence (isEquivalence s₁) (isEquivalence s₂)
    } where open Setoid

  ×-decSetoid : DecSetoid ℓ₁ ℓ₂ → DecSetoid ℓ₃ ℓ₄ → DecSetoid _ _
  ×-decSetoid s₁ s₂ = record
    { isDecEquivalence =
        ×-isDecEquivalence (isDecEquivalence s₁) (isDecEquivalence s₂)
    } where open DecSetoid

  ×-poset : Poset ℓ₁ ℓ₂ _ → Poset ℓ₃ ℓ₄ _ → Poset _ _ _
  ×-poset s₁ s₂ = record
    { isPartialOrder = ×-isPartialOrder (isPartialOrder s₁)
                       (isPartialOrder s₂)
    } where open Poset

  ×-strictPartialOrder :
    StrictPartialOrder ℓ₁ ℓ₂ _ → StrictPartialOrder ℓ₃ ℓ₄ _ →
    StrictPartialOrder _ _ _
  ×-strictPartialOrder s₁ s₂ = record
    { isStrictPartialOrder = ×-isStrictPartialOrder
                               (isStrictPartialOrder s₁)
                               (isStrictPartialOrder s₂)
    } where open StrictPartialOrder

  -- A piece of infix notation for combining setoids
  infix 4 _×ₛ_
  _×ₛ_ : Setoid ℓ₁ ℓ₂ → Setoid ℓ₃ ℓ₄ → Setoid _ _
  _×ₛ_ = ×-setoid

------------------------------------------------------------------------
-- The propositional equality setoid over products can be
-- decomposed using ×-Rel

module _ {a b} {A : Set a} {B : Set b} where

  ≡×≡⇒≡ : Pointwise _≡_ _≡_ ⇒ _≡_ {A = A × B}
  ≡×≡⇒≡ (P.refl , P.refl) = P.refl

  ≡⇒≡×≡ : _≡_ {A = A × B} ⇒ Pointwise _≡_ _≡_
  ≡⇒≡×≡ P.refl = (P.refl , P.refl)

  Pointwise-≡↔≡ : Inverse (×-setoid (P.setoid A) (P.setoid B))
                          (P.setoid (A × B))
  Pointwise-≡↔≡ = record
    { to         = record { _⟨$⟩_ = id; cong = ≡×≡⇒≡ }
    ; from       = record { _⟨$⟩_ = id; cong = ≡⇒≡×≡ }
    ; inverse-of = record
      { left-inverse-of  = λ _ → (P.refl , P.refl)
      ; right-inverse-of = λ _ → P.refl
      }
    }

  ≡?×≡?⇒≡? : Decidable {A = A} _≡_ → Decidable {A = B} _≡_ →
          Decidable {A = A × B} _≡_
  ≡?×≡?⇒≡? ≟₁ ≟₂ p₁ p₂ =
    Dec.map′ ≡×≡⇒≡ ≡⇒≡×≡ (×-decidable ≟₁ ≟₂ p₁ p₂)

------------------------------------------------------------------------
-- Some properties related to "relatedness"

_×-⟶_ : ∀ {a₁ a₂ b₁ b₂ c₁ c₂ d₁ d₂}
  {A : Setoid a₁ a₂} {B : Setoid b₁ b₂}
  {C : Setoid c₁ c₂} {D : Setoid d₁ d₂} →
  A ⟶ B → C ⟶ D → (A ×ₛ C) ⟶ (B ×ₛ D)
_×-⟶_ {A = A} {B} {C} {D} f g = record
  { _⟨$⟩_ = fg
  ; cong  = fg-cong
  }
  where
  open Setoid (A ×ₛ C) using () renaming (_≈_ to _≈AC_)
  open Setoid (B ×ₛ D) using () renaming (_≈_ to _≈BD_)

  fg = Prod.map (f ⟨$⟩_) (g ⟨$⟩_)

  fg-cong : _≈AC_ =[ fg ]⇒ _≈BD_
  fg-cong (_∼₁_ , _∼₂_) = (F.cong f _∼₁_ , F.cong g _∼₂_)

module _ {a₁ a₂ b₁ b₂ c₁ c₂ d₁ d₂}
  {A : Setoid a₁ a₂} {B : Setoid b₁ b₂}
  {C : Setoid c₁ c₂} {D : Setoid d₁ d₂}
  where

  _×-equivalence_ : Equivalence A B → Equivalence C D →
                    Equivalence (A ×ₛ C) (B ×ₛ D)
  _×-equivalence_ A⇔B C⇔D = record
    { to   = to   A⇔B ×-⟶ to   C⇔D
    ; from = from A⇔B ×-⟶ from C⇔D
    } where open Equivalence

  _×-injection_ : Injection A B → Injection C D →
                  Injection (A ×ₛ C) (B ×ₛ D)
  A↣B ×-injection C↣D = record
    { to        = to A↣B ×-⟶ to C↣D
    ; injective = Prod.map (injective A↣B) (injective C↣D)
    } where open Injection

  _×-left-inverse_ : LeftInverse A B → LeftInverse C D →
                     LeftInverse (A ×ₛ C) (B ×ₛ D)
  A↞B ×-left-inverse C↞D = record
    { to              = Equivalence.to eq
    ; from            = Equivalence.from eq
    ; left-inverse-of = left
    }
    where
    open LeftInverse
    eq = LeftInverse.equivalence A↞B ×-equivalence
         LeftInverse.equivalence C↞D

    left : Equivalence.from eq LeftInverseOf Equivalence.to eq
    left (x , y) = (left-inverse-of A↞B x , left-inverse-of C↞D y)

module _ {a₁ a₂ b₁ b₂ c₁ c₂ d₁ d₂}
  {A : Setoid a₁ a₂} {B : Setoid b₁ b₂}
  {C : Setoid c₁ c₂} {D : Setoid d₁ d₂}
  where

  _×-surjection_ : Surjection A B → Surjection C D →
                   Surjection (A ×ₛ C) (B ×ₛ D)
  A↠B ×-surjection C↠D = record
    { to         = LeftInverse.from inv
    ; surjective = record
      { from             = LeftInverse.to inv
      ; right-inverse-of = LeftInverse.left-inverse-of inv
      }
    }
    where
    open Surjection
    inv = right-inverse A↠B ×-left-inverse right-inverse C↠D

  _×-inverse_ : Inverse A B → Inverse C D →
                Inverse (A ×ₛ C) (B ×ₛ D)
  A↔B ×-inverse C↔D = record
    { to         = Surjection.to   surj
    ; from       = Surjection.from surj
    ; inverse-of = record
      { left-inverse-of  = LeftInverse.left-inverse-of inv
      ; right-inverse-of = Surjection.right-inverse-of surj
      }
    }
    where
    open Inverse
    surj = Inverse.surjection   A↔B ×-surjection
           Inverse.surjection   C↔D
    inv  = Inverse.left-inverse A↔B ×-left-inverse
           Inverse.left-inverse C↔D

------------------------------------------------------------------------

module _ {a b c d} {A : Set a} {B : Set b} {C : Set c} {D : Set d} where

  _×-⇔_ : A ⇔ B → C ⇔ D → (A × C) ⇔ (B × D)
  _×-⇔_ A⇔B C⇔D =
    Inverse.equivalence Pointwise-≡↔≡           ⟨∘⟩
    (A⇔B ×-equivalence C⇔D)                     ⟨∘⟩
    Eq.sym (Inverse.equivalence Pointwise-≡↔≡)
    where open Eq using () renaming (_∘_ to _⟨∘⟩_)

  _×-↣_ : A ↣ B → C ↣ D → (A × C) ↣ (B × D)
  _×-↣_ A↣B C↣D =
    Inverse.injection Pointwise-≡↔≡           ⟨∘⟩
    (A↣B ×-injection C↣D)                     ⟨∘⟩
    Inverse.injection (Inv.sym Pointwise-≡↔≡)
    where open Inj using () renaming (_∘_ to _⟨∘⟩_)

  _×-↞_ : A ↞ B → C ↞ D → (A × C) ↞ (B × D)
  _×-↞_ A↞B C↞D =
    Inverse.left-inverse Pointwise-≡↔≡           ⟨∘⟩
    (A↞B ×-left-inverse C↞D)                     ⟨∘⟩
    Inverse.left-inverse (Inv.sym Pointwise-≡↔≡)
    where open LeftInv using () renaming (_∘_ to _⟨∘⟩_)

  _×-↠_ : A ↠ B → C ↠ D → (A × C) ↠ (B × D)
  _×-↠_ A↠B C↠D =
    Inverse.surjection Pointwise-≡↔≡           ⟨∘⟩
    (A↠B ×-surjection C↠D)                     ⟨∘⟩
    Inverse.surjection (Inv.sym Pointwise-≡↔≡)
    where open Surj using () renaming (_∘_ to _⟨∘⟩_)

  _×-↔_ : A ↔ B → C ↔ D → (A × C) ↔ (B × D)
  _×-↔_ A↔B C↔D =
    Pointwise-≡↔≡          ⟨∘⟩
    (A↔B ×-inverse C↔D)    ⟨∘⟩
    Inv.sym Pointwise-≡↔≡
    where open Inv using () renaming (_∘_ to _⟨∘⟩_)

_×-cong_ : ∀ {k a b c d} {A : Set a} {B : Set b} {C : Set c} {D : Set d} →
           A ∼[ k ] B → C ∼[ k ] D → (A × C) ∼[ k ] (B × D)
_×-cong_ {implication}         = λ f g →      Prod.map        f         g
_×-cong_ {reverse-implication} = λ f g → lam (Prod.map (app-← f) (app-← g))
_×-cong_ {equivalence}         = _×-⇔_
_×-cong_ {injection}           = _×-↣_
_×-cong_ {reverse-injection}   = λ f g → lam (app-↢ f ×-↣ app-↢ g)
_×-cong_ {left-inverse}        = _×-↞_
_×-cong_ {surjection}          = _×-↠_
_×-cong_ {bijection}           = _×-↔_

------------------------------------------------------------------------
-- DEPRECATED NAMES
------------------------------------------------------------------------
-- Please use the new names as continuing support for the old names is
-- not guaranteed.

infixr 2 _×-Rel_
_×-Rel_ = Pointwise

Rel↔≡                     = Pointwise-≡↔≡
_×-reflexive_             = ×-reflexive
_×-refl_                  = ×-refl
_×-symmetric_             = ×-symmetric
_×-transitive_            = ×-transitive
_×-antisymmetric_         = ×-antisymmetric
_×-≈-respects₂_           = ×-respects₂
_×-decidable_             = ×-decidable
_×-isEquivalence_         = ×-isEquivalence
_×-isDecEquivalence_      = ×-isDecEquivalence
_×-isPreorder_            = ×-isPreorder
_×-isPartialOrder_        = ×-isPartialOrder
_×-isStrictPartialOrder_  = ×-isStrictPartialOrder
_×-preorder_              = ×-preorder
_×-setoid_                = ×-setoid
_×-decSetoid_             = ×-decSetoid
_×-poset_                 = ×-poset
_×-strictPartialOrder_    = ×-strictPartialOrder
_×-≟_                     = ≡?×≡?⇒≡?
