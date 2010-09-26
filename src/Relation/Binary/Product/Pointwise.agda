------------------------------------------------------------------------
-- Pointwise products of binary relations
------------------------------------------------------------------------

{-# OPTIONS --universe-polymorphism #-}

module Relation.Binary.Product.Pointwise where

open import Data.Product as Prod
open import Data.Sum
open import Data.Unit using (⊤)
open import Function
open import Function.Equality as F using (_⟨$⟩_)
open import Function.Equivalence as Eq
  using (Equivalent; _⇔_; module Equivalent)
  renaming (_∘_ to _⟨∘⟩_)
open import Function.Inverse as Inv
  using (Inverse; _⇿_; module Inverse)
  renaming (_∘_ to _⟪∘⟫_)
open import Function.LeftInverse
  using (_LeftInverseOf_; _RightInverseOf_)
open import Level
open import Relation.Nullary.Product
open import Relation.Binary
import Relation.Binary.PropositionalEquality as P

private
 module Dummy {a₁ a₂ ℓ₁ ℓ₂} {A₁ : Set a₁} {A₂ : Set a₂} where

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

open Dummy public

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
-- Some properties related to equivalences and inverses

×-Rel⇿≡ : ∀ {a b} {A : Set a} {B : Set b} →
          Inverse (P.setoid A ×-setoid P.setoid B) (P.setoid (A × B))
×-Rel⇿≡ {A = A} {B} = record
  { to         = record { _⟨$⟩_ = id; cong = to-cong   }
  ; from       = record { _⟨$⟩_ = id; cong = from-cong }
  ; inverse-of = record
    { left-inverse-of  = λ _ → (P.refl , P.refl)
    ; right-inverse-of = λ _ → P.refl
    }
  }
  where
  to-cong : (P._≡_ ×-Rel P._≡_) ⇒ P._≡_
  to-cong (eq₁ , eq₂) = helper eq₁ eq₂
    where
    open P using (_≡_)

    helper : {x x′ : A} {y y′ : B} →
             x ≡ x′ → y ≡ y′ → _≡_ {A = A × B} (x , y) (x′ , y′)
    helper P.refl P.refl = P.refl

  from-cong : P._≡_ ⇒ (P._≡_ ×-Rel P._≡_)
  from-cong P.refl = (P.refl , P.refl)

_×-equivalent_ :
  ∀ {a₁ a₂ b₁ b₂ c₁ c₂ d₁ d₂}
    {A : Setoid a₁ a₂} {B : Setoid b₁ b₂}
    {C : Setoid c₁ c₂} {D : Setoid d₁ d₂} →
  Equivalent A B → Equivalent C D →
  Equivalent (A ×-setoid C) (B ×-setoid D)
_×-equivalent_ {A = A} {B} {C} {D} A⇔B C⇔D = record
  { to   = record { _⟨$⟩_ = to;   cong = λ {x y} → to-cong   {x} {y} }
  ; from = record { _⟨$⟩_ = from; cong = λ {x y} → from-cong {x} {y} }
  }
  where
  open Setoid (A ×-setoid C) using () renaming (_≈_ to _≈AC_)
  open Setoid (B ×-setoid D) using () renaming (_≈_ to _≈BD_)

  to = Prod.map (_⟨$⟩_ (Equivalent.to A⇔B))
                (_⟨$⟩_ (Equivalent.to C⇔D))

  to-cong : _≈AC_ =[ to ]⇒ _≈BD_
  to-cong (_∼₁_ , _∼₂_) =
    (F.cong (Equivalent.to A⇔B) _∼₁_ , F.cong (Equivalent.to C⇔D) _∼₂_)

  from = Prod.map (_⟨$⟩_ (Equivalent.from A⇔B))
                  (_⟨$⟩_ (Equivalent.from C⇔D))

  from-cong : _≈BD_ =[ from ]⇒ _≈AC_
  from-cong (_∼₁_ , _∼₂_) =
    (F.cong (Equivalent.from A⇔B) _∼₁_ ,
     F.cong (Equivalent.from C⇔D) _∼₂_)

_×-⇔_ : ∀ {a b c d} {A : Set a} {B : Set b} {C : Set c} {D : Set d} →
        A ⇔ B → C ⇔ D → (A × C) ⇔ (B × D)
_×-⇔_ {A = A} {B} {C} {D} A⇔B C⇔D =
  Inverse.equivalent (×-Rel⇿≡ {A = B} {B = D}) ⟨∘⟩
  A⇔B ×-equivalent C⇔D ⟨∘⟩
  Eq.sym (Inverse.equivalent (×-Rel⇿≡ {A = A} {B = C}))

_×-inverse_ :
  ∀ {a₁ a₂ b₁ b₂ c₁ c₂ d₁ d₂}
    {A : Setoid a₁ a₂} {B : Setoid b₁ b₂}
    {C : Setoid c₁ c₂} {D : Setoid d₁ d₂} →
  Inverse A B → Inverse C D → Inverse (A ×-setoid C) (B ×-setoid D)
A⇿B ×-inverse C⇿D = record
  { to         = Equivalent.to   eq
  ; from       = Equivalent.from eq
  ; inverse-of = record
    { left-inverse-of  = left
    ; right-inverse-of = right
    }
  }
  where
  eq = Inverse.equivalent A⇿B ×-equivalent Inverse.equivalent C⇿D

  left : Equivalent.from eq LeftInverseOf Equivalent.to eq
  left (x , y) = ( Inverse.left-inverse-of A⇿B x
                 , Inverse.left-inverse-of C⇿D y
                 )

  right : Equivalent.from eq RightInverseOf Equivalent.to eq
  right (x , y) = ( Inverse.right-inverse-of A⇿B x
                  , Inverse.right-inverse-of C⇿D y
                  )

_×-⇿_ : ∀ {a b c d} {A : Set a} {B : Set b} {C : Set c} {D : Set d} →
        A ⇿ B → C ⇿ D → (A × C) ⇿ (B × D)
_×-⇿_ {A = A} {B} {C} {D} A⇿B C⇿D =
  ×-Rel⇿≡ {A = B} {B = D} ⟪∘⟫
  A⇿B ×-inverse C⇿D ⟪∘⟫
  Inv.sym (×-Rel⇿≡ {A = A} {B = C})
