------------------------------------------------------------------------
-- The Agda standard library
--
-- Pointwise products of binary relations
------------------------------------------------------------------------

module Relation.Binary.Product.Pointwise where

open import Data.Product as Prod
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
open import Level
import Relation.Nullary.Decidable as Dec
open import Relation.Nullary.Product
open import Relation.Binary
open import Relation.Binary.PropositionalEquality as P using (_≡_)

module _ {a₁ a₂ ℓ₁ ℓ₂} {A₁ : Set a₁} {A₂ : Set a₂} where

  infixr 2 _×-Rel_

  _×-Rel_ : Rel A₁ ℓ₁ → Rel A₂ ℓ₂ → Rel (A₁ × A₂) _
  _∼₁_ ×-Rel _∼₂_ = (_∼₁_ on proj₁) -×- (_∼₂_ on proj₂)

  -- Some properties which are preserved by ×-Rel (under certain
  -- assumptions).

  _×-reflexive_ :
    ∀ {_≈₁_ _∼₁_ _≈₂_ _∼₂_} →
    _≈₁_ ⇒ _∼₁_ → _≈₂_ ⇒ _∼₂_ → (_≈₁_ ×-Rel _≈₂_) ⇒ (_∼₁_ ×-Rel _∼₂_)
  refl₁ ×-reflexive refl₂ = λ x≈y →
    (refl₁ (proj₁ x≈y) , refl₂ (proj₂ x≈y))

  _×-refl_ :
    ∀ {_∼₁_ _∼₂_} →
    Reflexive _∼₁_ → Reflexive _∼₂_ → Reflexive (_∼₁_ ×-Rel _∼₂_)
  refl₁ ×-refl refl₂ = (refl₁ , refl₂)

  ×-irreflexive₁ :
    ∀ {_≈₁_ _<₁_ _≈₂_ _<₂_} →
    Irreflexive _≈₁_ _<₁_ →
    Irreflexive (_≈₁_ ×-Rel _≈₂_) (_<₁_ ×-Rel _<₂_)
  ×-irreflexive₁ ir = λ x≈y x<y → ir (proj₁ x≈y) (proj₁ x<y)

  ×-irreflexive₂ :
    ∀ {_≈₁_ _<₁_ _≈₂_ _<₂_} →
    Irreflexive _≈₂_ _<₂_ →
    Irreflexive (_≈₁_ ×-Rel _≈₂_) (_<₁_ ×-Rel _<₂_)
  ×-irreflexive₂ ir = λ x≈y x<y → ir (proj₂ x≈y) (proj₂ x<y)

  _×-symmetric_ :
    ∀ {_∼₁_ _∼₂_} →
    Symmetric _∼₁_ → Symmetric _∼₂_ → Symmetric (_∼₁_ ×-Rel _∼₂_)
  sym₁ ×-symmetric sym₂ = λ x∼y → sym₁ (proj₁ x∼y) , sym₂ (proj₂ x∼y)

  _×-transitive_ : ∀ {_∼₁_ _∼₂_} →
                   Transitive _∼₁_ → Transitive _∼₂_ →
                   Transitive (_∼₁_ ×-Rel _∼₂_)
  trans₁ ×-transitive trans₂ = λ x∼y y∼z →
    trans₁ (proj₁ x∼y) (proj₁ y∼z) ,
    trans₂ (proj₂ x∼y) (proj₂ y∼z)

  _×-antisymmetric_ :
    ∀ {_≈₁_ _≤₁_ _≈₂_ _≤₂_} →
    Antisymmetric _≈₁_ _≤₁_ → Antisymmetric _≈₂_ _≤₂_ →
    Antisymmetric (_≈₁_ ×-Rel _≈₂_) (_≤₁_ ×-Rel _≤₂_)
  antisym₁ ×-antisymmetric antisym₂ = λ x≤y y≤x →
    ( antisym₁ (proj₁ x≤y) (proj₁ y≤x)
    , antisym₂ (proj₂ x≤y) (proj₂ y≤x) )

  ×-asymmetric₁ :
    ∀ {_<₁_ _∼₂_} → Asymmetric _<₁_ → Asymmetric (_<₁_ ×-Rel _∼₂_)
  ×-asymmetric₁ asym₁ = λ x<y y<x → asym₁ (proj₁ x<y) (proj₁ y<x)

  ×-asymmetric₂ :
    ∀ {_∼₁_ _<₂_} → Asymmetric _<₂_ → Asymmetric (_∼₁_ ×-Rel _<₂_)
  ×-asymmetric₂ asym₂ = λ x<y y<x → asym₂ (proj₂ x<y) (proj₂ y<x)

  _×-≈-respects₂_ : ∀ {_≈₁_ _∼₁_ _≈₂_ _∼₂_} →
                    _∼₁_ Respects₂ _≈₁_ → _∼₂_ Respects₂ _≈₂_ →
                    (_∼₁_ ×-Rel _∼₂_) Respects₂ (_≈₁_ ×-Rel _≈₂_)
  _×-≈-respects₂_
    {_≈₁_ = _≈₁_} {_∼₁_ = _∼₁_} {_≈₂_ = _≈₂_} {_∼₂_ = _∼₂_}
    resp₁ resp₂ =
    (λ {x y z} → resp¹ {x} {y} {z}) ,
    (λ {x y z} → resp² {x} {y} {z})
    where
    _∼_ = _∼₁_ ×-Rel _∼₂_

    resp¹ : ∀ {x} → (_∼_ x) Respects (_≈₁_ ×-Rel _≈₂_)
    resp¹ y≈y' x∼y = proj₁ resp₁ (proj₁ y≈y') (proj₁ x∼y) ,
                     proj₁ resp₂ (proj₂ y≈y') (proj₂ x∼y)

    resp² : ∀ {y} → (flip _∼_ y) Respects (_≈₁_ ×-Rel _≈₂_)
    resp² x≈x' x∼y = proj₂ resp₁ (proj₁ x≈x') (proj₁ x∼y) ,
                     proj₂ resp₂ (proj₂ x≈x') (proj₂ x∼y)

  ×-total :
    ∀ {_∼₁_ _∼₂_} →
    Symmetric _∼₁_ → Total _∼₁_ → Total _∼₂_ → Total (_∼₁_ ×-Rel _∼₂_)
  ×-total {_∼₁_ = _∼₁_} {_∼₂_ = _∼₂_} sym₁ total₁ total₂ = total
    where
    total : Total (_∼₁_ ×-Rel _∼₂_)
    total x y with total₁ (proj₁ x) (proj₁ y)
                 | total₂ (proj₂ x) (proj₂ y)
    ... | inj₁ x₁∼y₁ | inj₁ x₂∼y₂ = inj₁ (     x₁∼y₁ , x₂∼y₂)
    ... | inj₁ x₁∼y₁ | inj₂ y₂∼x₂ = inj₂ (sym₁ x₁∼y₁ , y₂∼x₂)
    ... | inj₂ y₁∼x₁ | inj₂ y₂∼x₂ = inj₂ (     y₁∼x₁ , y₂∼x₂)
    ... | inj₂ y₁∼x₁ | inj₁ x₂∼y₂ = inj₁ (sym₁ y₁∼x₁ , x₂∼y₂)

  _×-decidable_ :
    ∀ {_∼₁_ _∼₂_} →
    Decidable _∼₁_ → Decidable _∼₂_ → Decidable (_∼₁_ ×-Rel _∼₂_)
  dec₁ ×-decidable dec₂ = λ x y →
    dec₁ (proj₁ x) (proj₁ y)
      ×-dec
    dec₂ (proj₂ x) (proj₂ y)

  -- Some collections of properties which are preserved by ×-Rel.

  _×-isEquivalence_ : ∀ {_≈₁_ _≈₂_} →
                      IsEquivalence _≈₁_ → IsEquivalence _≈₂_ →
                      IsEquivalence (_≈₁_ ×-Rel _≈₂_)
  _×-isEquivalence_ {_≈₁_ = _≈₁_} {_≈₂_ = _≈₂_} eq₁ eq₂ = record
    { refl  = λ {x} →
              _×-refl_        {_∼₁_ = _≈₁_} {_∼₂_ = _≈₂_}
                              (refl  eq₁) (refl  eq₂) {x}
    ; sym   = λ {x y} →
              _×-symmetric_   {_∼₁_ = _≈₁_} {_∼₂_ = _≈₂_}
                              (sym   eq₁) (sym   eq₂) {x} {y}
    ; trans = λ {x y z} →
              _×-transitive_  {_∼₁_ = _≈₁_} {_∼₂_ = _≈₂_}
                              (trans eq₁) (trans eq₂) {x} {y} {z}
    }
    where open IsEquivalence

  _×-isPreorder_ : ∀ {_≈₁_ _∼₁_ _≈₂_ _∼₂_} →
                   IsPreorder _≈₁_ _∼₁_ → IsPreorder _≈₂_ _∼₂_ →
                   IsPreorder (_≈₁_ ×-Rel _≈₂_) (_∼₁_ ×-Rel _∼₂_)
  _×-isPreorder_ {_∼₁_ = _∼₁_} {_∼₂_ = _∼₂_} pre₁ pre₂ = record
    { isEquivalence = isEquivalence pre₁ ×-isEquivalence
                      isEquivalence pre₂
    ; reflexive     = λ {x y} →
                      _×-reflexive_  {_∼₁_ = _∼₁_} {_∼₂_ = _∼₂_}
                                     (reflexive pre₁) (reflexive pre₂)
                                     {x} {y}
    ; trans         = λ {x y z} →
                      _×-transitive_ {_∼₁_ = _∼₁_} {_∼₂_ = _∼₂_}
                                     (trans pre₁) (trans pre₂)
                                     {x} {y} {z}
    }
    where open IsPreorder

  _×-isDecEquivalence_ :
    ∀ {_≈₁_ _≈₂_} →
    IsDecEquivalence _≈₁_ → IsDecEquivalence _≈₂_ →
    IsDecEquivalence (_≈₁_ ×-Rel _≈₂_)
  eq₁ ×-isDecEquivalence eq₂ = record
    { isEquivalence = isEquivalence eq₁ ×-isEquivalence
                      isEquivalence eq₂
    ; _≟_           = _≟_ eq₁ ×-decidable _≟_ eq₂
    }
    where open IsDecEquivalence

  _×-isPartialOrder_ :
    ∀ {_≈₁_ _≤₁_ _≈₂_ _≤₂_} →
    IsPartialOrder _≈₁_ _≤₁_ → IsPartialOrder _≈₂_ _≤₂_ →
    IsPartialOrder (_≈₁_ ×-Rel _≈₂_) (_≤₁_ ×-Rel _≤₂_)
  _×-isPartialOrder_ {_≤₁_ = _≤₁_} {_≤₂_ = _≤₂_} po₁ po₂ = record
    { isPreorder = isPreorder po₁ ×-isPreorder isPreorder po₂
    ; antisym    = λ {x y} →
                   _×-antisymmetric_ {_≤₁_ = _≤₁_} {_≤₂_ = _≤₂_}
                                     (antisym po₁) (antisym po₂)
                                     {x} {y}
    }
    where open IsPartialOrder

  _×-isStrictPartialOrder_ :
    ∀ {_≈₁_ _<₁_ _≈₂_ _<₂_} →
    IsStrictPartialOrder _≈₁_ _<₁_ → IsStrictPartialOrder _≈₂_ _<₂_ →
    IsStrictPartialOrder (_≈₁_ ×-Rel _≈₂_) (_<₁_ ×-Rel _<₂_)
  _×-isStrictPartialOrder_ {_<₁_ = _<₁_} {_≈₂_ = _≈₂_} {_<₂_ = _<₂_}
                           spo₁ spo₂ =
    record
      { isEquivalence = isEquivalence spo₁ ×-isEquivalence
                        isEquivalence spo₂
      ; irrefl        = λ {x y} →
                        ×-irreflexive₁ {_<₁_ = _<₁_}
                                       {_≈₂_ = _≈₂_} {_<₂_ = _<₂_}
                                       (irrefl spo₁) {x} {y}
      ; trans         = λ {x y z} →
                        _×-transitive_ {_∼₁_ = _<₁_} {_∼₂_ = _<₂_}
                                       (trans spo₁) (trans spo₂)
                                       {x} {y} {z}
      ; <-resp-≈      = <-resp-≈ spo₁ ×-≈-respects₂ <-resp-≈ spo₂
      }
    where open IsStrictPartialOrder

-- "Packages" (e.g. setoids) can also be combined.

_×-preorder_ :
  ∀ {p₁ p₂ p₃ p₄} →
  Preorder p₁ p₂ _ → Preorder p₃ p₄ _ → Preorder _ _ _
p₁ ×-preorder p₂ = record
  { isPreorder = isPreorder p₁ ×-isPreorder isPreorder p₂
  } where open Preorder

_×-setoid_ :
  ∀ {s₁ s₂ s₃ s₄} → Setoid s₁ s₂ → Setoid s₃ s₄ → Setoid _ _
s₁ ×-setoid s₂ = record
  { isEquivalence = isEquivalence s₁ ×-isEquivalence isEquivalence s₂
  } where open Setoid

_×-decSetoid_ :
  ∀ {d₁ d₂ d₃ d₄} → DecSetoid d₁ d₂ → DecSetoid d₃ d₄ → DecSetoid _ _
s₁ ×-decSetoid s₂ = record
  { isDecEquivalence = isDecEquivalence s₁ ×-isDecEquivalence
                       isDecEquivalence s₂
  } where open DecSetoid

_×-poset_ :
  ∀ {p₁ p₂ p₃ p₄} → Poset p₁ p₂ _ → Poset p₃ p₄ _ → Poset _ _ _
s₁ ×-poset s₂ = record
  { isPartialOrder = isPartialOrder s₁ ×-isPartialOrder
                     isPartialOrder s₂
  } where open Poset

_×-strictPartialOrder_ :
  ∀ {s₁ s₂ s₃ s₄} →
  StrictPartialOrder s₁ s₂ _ → StrictPartialOrder s₃ s₄ _ →
  StrictPartialOrder _ _ _
s₁ ×-strictPartialOrder s₂ = record
  { isStrictPartialOrder = isStrictPartialOrder s₁
                             ×-isStrictPartialOrder
                           isStrictPartialOrder s₂
  } where open StrictPartialOrder

------------------------------------------------------------------------
-- Some properties related to "relatedness"

private

  to-cong : ∀ {a b} {A : Set a} {B : Set b} →
            (_≡_ ×-Rel _≡_) ⇒ _≡_ {A = A × B}
  to-cong {i = (x , y)} {j = (.x , .y)} (P.refl , P.refl) = P.refl

  from-cong : ∀ {a b} {A : Set a} {B : Set b} →
              _≡_ {A = A × B} ⇒ (_≡_ ×-Rel _≡_)
  from-cong P.refl = (P.refl , P.refl)

×-Rel↔≡ : ∀ {a b} {A : Set a} {B : Set b} →
          Inverse (P.setoid A ×-setoid P.setoid B) (P.setoid (A × B))
×-Rel↔≡ = record
  { to         = record { _⟨$⟩_ = id; cong = to-cong   }
  ; from       = record { _⟨$⟩_ = id; cong = from-cong }
  ; inverse-of = record
    { left-inverse-of  = λ _ → (P.refl , P.refl)
    ; right-inverse-of = λ _ → P.refl
    }
  }

_×-≟_ : ∀ {a b} {A : Set a} {B : Set b} →
        Decidable {A = A} _≡_ → Decidable {A = B} _≡_ →
        Decidable {A = A × B} _≡_
(dec₁ ×-≟ dec₂) p₁ p₂ = Dec.map′ to-cong from-cong (p₁ ≟ p₂)
  where
  open DecSetoid (P.decSetoid dec₁ ×-decSetoid P.decSetoid dec₂)

_×-⟶_ :
  ∀ {s₁ s₂ s₃ s₄ s₅ s₆ s₇ s₈}
    {A : Setoid s₁ s₂} {B : Setoid s₃ s₄}
    {C : Setoid s₅ s₆} {D : Setoid s₇ s₈} →
  A ⟶ B → C ⟶ D → (A ×-setoid C) ⟶ (B ×-setoid D)
_×-⟶_ {A = A} {B} {C} {D} f g = record
  { _⟨$⟩_ = fg
  ; cong  = fg-cong
  }
  where
  open Setoid (A ×-setoid C) using () renaming (_≈_ to _≈AC_)
  open Setoid (B ×-setoid D) using () renaming (_≈_ to _≈BD_)

  fg = Prod.map (_⟨$⟩_ f) (_⟨$⟩_ g)

  fg-cong : _≈AC_ =[ fg ]⇒ _≈BD_
  fg-cong (_∼₁_ , _∼₂_) = (F.cong f _∼₁_ , F.cong g _∼₂_)

_×-equivalence_ :
  ∀ {a₁ a₂ b₁ b₂ c₁ c₂ d₁ d₂}
    {A : Setoid a₁ a₂} {B : Setoid b₁ b₂}
    {C : Setoid c₁ c₂} {D : Setoid d₁ d₂} →
  Equivalence A B → Equivalence C D →
  Equivalence (A ×-setoid C) (B ×-setoid D)
_×-equivalence_ {A = A} {B} {C} {D} A⇔B C⇔D = record
  { to   = to   A⇔B ×-⟶ to   C⇔D
  ; from = from A⇔B ×-⟶ from C⇔D
  } where open Equivalence

_×-⇔_ : ∀ {a b c d} {A : Set a} {B : Set b} {C : Set c} {D : Set d} →
        A ⇔ B → C ⇔ D → (A × C) ⇔ (B × D)
_×-⇔_ {A = A} {B} {C} {D} A⇔B C⇔D =
  Inverse.equivalence (×-Rel↔≡ {A = B} {B = D}) ⟨∘⟩
  (A⇔B ×-equivalence C⇔D) ⟨∘⟩
  Eq.sym (Inverse.equivalence (×-Rel↔≡ {A = A} {B = C}))
  where open Eq using () renaming (_∘_ to _⟨∘⟩_)

_×-injection_ :
  ∀ {s₁ s₂ s₃ s₄ s₅ s₆ s₇ s₈}
    {A : Setoid s₁ s₂} {B : Setoid s₃ s₄}
    {C : Setoid s₅ s₆} {D : Setoid s₇ s₈} →
  Injection A B → Injection C D →
  Injection (A ×-setoid C) (B ×-setoid D)
A↣B ×-injection C↣D = record
  { to        = to A↣B ×-⟶ to C↣D
  ; injective = Prod.map (injective A↣B) (injective C↣D)
  } where open Injection

_×-↣_ : ∀ {a b c d} {A : Set a} {B : Set b} {C : Set c} {D : Set d} →
        A ↣ B → C ↣ D → (A × C) ↣ (B × D)
_×-↣_ {A = A} {B} {C} {D} A↣B C↣D =
  Inverse.injection (×-Rel↔≡ {A = B} {B = D}) ⟨∘⟩
  (A↣B ×-injection C↣D) ⟨∘⟩
  Inverse.injection (Inv.sym (×-Rel↔≡ {A = A} {B = C}))
  where open Inj using () renaming (_∘_ to _⟨∘⟩_)

_×-left-inverse_ :
  ∀ {s₁ s₂ s₃ s₄ s₅ s₆ s₇ s₈}
    {A : Setoid s₁ s₂} {B : Setoid s₃ s₄}
    {C : Setoid s₅ s₆} {D : Setoid s₇ s₈} →
  LeftInverse A B → LeftInverse C D →
  LeftInverse (A ×-setoid C) (B ×-setoid D)
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
  left (x , y) = ( left-inverse-of A↞B x
                 , left-inverse-of C↞D y
                 )

_×-↞_ : ∀ {a b c d} {A : Set a} {B : Set b} {C : Set c} {D : Set d} →
        A ↞ B → C ↞ D → (A × C) ↞ (B × D)
_×-↞_ {A = A} {B} {C} {D} A↞B C↞D =
  Inverse.left-inverse (×-Rel↔≡ {A = B} {B = D}) ⟨∘⟩
  (A↞B ×-left-inverse C↞D) ⟨∘⟩
  Inverse.left-inverse (Inv.sym (×-Rel↔≡ {A = A} {B = C}))
  where open LeftInv using () renaming (_∘_ to _⟨∘⟩_)

_×-surjection_ :
  ∀ {s₁ s₂ s₃ s₄ s₅ s₆ s₇ s₈}
    {A : Setoid s₁ s₂} {B : Setoid s₃ s₄}
    {C : Setoid s₅ s₆} {D : Setoid s₇ s₈} →
  Surjection A B → Surjection C D →
  Surjection (A ×-setoid C) (B ×-setoid D)
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

_×-↠_ : ∀ {a b c d} {A : Set a} {B : Set b} {C : Set c} {D : Set d} →
        A ↠ B → C ↠ D → (A × C) ↠ (B × D)
_×-↠_ {A = A} {B} {C} {D} A↠B C↠D =
  Inverse.surjection (×-Rel↔≡ {A = B} {B = D}) ⟨∘⟩
  (A↠B ×-surjection C↠D) ⟨∘⟩
  Inverse.surjection (Inv.sym (×-Rel↔≡ {A = A} {B = C}))
  where open Surj using () renaming (_∘_ to _⟨∘⟩_)

_×-inverse_ :
  ∀ {s₁ s₂ s₃ s₄ s₅ s₆ s₇ s₈}
    {A : Setoid s₁ s₂} {B : Setoid s₃ s₄}
    {C : Setoid s₅ s₆} {D : Setoid s₇ s₈} →
  Inverse A B → Inverse C D → Inverse (A ×-setoid C) (B ×-setoid D)
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

_×-↔_ : ∀ {a b c d} {A : Set a} {B : Set b} {C : Set c} {D : Set d} →
        A ↔ B → C ↔ D → (A × C) ↔ (B × D)
_×-↔_ {A = A} {B} {C} {D} A↔B C↔D =
  ×-Rel↔≡ {A = B} {B = D} ⟨∘⟩
  (A↔B ×-inverse C↔D) ⟨∘⟩
  Inv.sym (×-Rel↔≡ {A = A} {B = C})
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
