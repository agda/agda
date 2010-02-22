------------------------------------------------------------------------
-- Sums of binary relations
------------------------------------------------------------------------

module Relation.Binary.Sum where

open import Data.Sum as Sum
open import Data.Product
open import Data.Unit using (⊤)
open import Data.Empty
open import Function
open import Function.Equality as F using (_⟨$⟩_)
open import Function.Equivalence as Eq
  using (Equivalent; _⇔_; module Equivalent)
  renaming (_∘_ to _⟨∘⟩_)
open import Function.Inverse as Inv
  using (Inverse; _⇿_; module Inverse)
  renaming (_∘_ to _⟪∘⟫_)
open import Level
open import Relation.Nullary
open import Relation.Binary
import Relation.Binary.PropositionalEquality as P

private
 module Dummy {A₁ A₂ : Set} where

  ----------------------------------------------------------------------
  -- Sums of relations

  infixr 1 _⊎-Rel_ _⊎-<_

  -- Generalised sum.

  data ⊎ʳ (P : Set) (_∼₁_ : Rel A₁ zero) (_∼₂_ : Rel A₂ zero) :
          A₁ ⊎ A₂ → A₁ ⊎ A₂ → Set where
    ₁∼₂ : ∀ {x y} (p : P)         → ⊎ʳ P _∼₁_ _∼₂_ (inj₁ x) (inj₂ y)
    ₁∼₁ : ∀ {x y} (x∼₁y : x ∼₁ y) → ⊎ʳ P _∼₁_ _∼₂_ (inj₁ x) (inj₁ y)
    ₂∼₂ : ∀ {x y} (x∼₂y : x ∼₂ y) → ⊎ʳ P _∼₁_ _∼₂_ (inj₂ x) (inj₂ y)

  -- Pointwise sum.

  _⊎-Rel_ : Rel A₁ zero → Rel A₂ zero → Rel (A₁ ⊎ A₂) zero
  _⊎-Rel_ = ⊎ʳ ⊥

  -- All things to the left are smaller than (or equal to, depending
  -- on the underlying equality) all things to the right.

  _⊎-<_ : Rel A₁ zero → Rel A₂ zero → Rel (A₁ ⊎ A₂) zero
  _⊎-<_ = ⊎ʳ ⊤

  ----------------------------------------------------------------------
  -- Helpers

  private

    ₁≁₂ : {∼₁ : Rel A₁ zero} {∼₂ : Rel A₂ zero} →
          ∀ {x y} → ¬ (inj₁ x ⟨ ∼₁ ⊎-Rel ∼₂ ⟩ inj₂ y)
    ₁≁₂ (₁∼₂ ())

    drop-inj₁ : {∼₁ : Rel A₁ zero} {∼₂ : Rel A₂ zero} →
                ∀ {P x y} → inj₁ x ⟨ ⊎ʳ P ∼₁ ∼₂ ⟩ inj₁ y → ∼₁ x y
    drop-inj₁ (₁∼₁ x∼y) = x∼y

    drop-inj₂ : {∼₁ : Rel A₁ zero} {∼₂ : Rel A₂ zero} →
                ∀ {P x y} → inj₂ x ⟨ ⊎ʳ P ∼₁ ∼₂ ⟩ inj₂ y → ∼₂ x y
    drop-inj₂ (₂∼₂ x∼y) = x∼y

  ----------------------------------------------------------------------
  -- Some properties which are preserved by the relation formers above

  _⊎-reflexive_ : {≈₁ ∼₁ : Rel A₁ zero} → ≈₁ ⇒ ∼₁ →
                  {≈₂ ∼₂ : Rel A₂ zero} → ≈₂ ⇒ ∼₂ →
                  ∀ {P} → (≈₁ ⊎-Rel ≈₂) ⇒ (⊎ʳ P ∼₁ ∼₂)
  refl₁ ⊎-reflexive refl₂ = refl
    where
    refl : (_ ⊎-Rel _) ⇒ (⊎ʳ _ _ _)
    refl (₁∼₁ x₁≈y₁) = ₁∼₁ (refl₁ x₁≈y₁)
    refl (₂∼₂ x₂≈y₂) = ₂∼₂ (refl₂ x₂≈y₂)
    refl (₁∼₂ ())

  _⊎-refl_ : {∼₁ : Rel A₁ zero} → Reflexive ∼₁ →
             {∼₂ : Rel A₂ zero} → Reflexive ∼₂ →
             Reflexive (∼₁ ⊎-Rel ∼₂)
  refl₁ ⊎-refl refl₂ = refl
    where
    refl : Reflexive (_ ⊎-Rel _)
    refl {x = inj₁ _} = ₁∼₁ refl₁
    refl {x = inj₂ _} = ₂∼₂ refl₂

  _⊎-irreflexive_ : {≈₁ <₁ : Rel A₁ zero} → Irreflexive ≈₁ <₁ →
                    {≈₂ <₂ : Rel A₂ zero} → Irreflexive ≈₂ <₂ →
                    ∀ {P} → Irreflexive (≈₁ ⊎-Rel ≈₂) (⊎ʳ P <₁ <₂)
  irrefl₁ ⊎-irreflexive irrefl₂ = irrefl
    where
    irrefl : Irreflexive (_ ⊎-Rel _) (⊎ʳ _ _ _)
    irrefl (₁∼₁ x₁≈y₁) (₁∼₁ x₁<y₁) = irrefl₁ x₁≈y₁ x₁<y₁
    irrefl (₂∼₂ x₂≈y₂) (₂∼₂ x₂<y₂) = irrefl₂ x₂≈y₂ x₂<y₂
    irrefl (₁∼₂ ())    _

  _⊎-symmetric_ : {∼₁ : Rel A₁ zero} → Symmetric ∼₁ →
                  {∼₂ : Rel A₂ zero} → Symmetric ∼₂ →
                  Symmetric (∼₁ ⊎-Rel ∼₂)
  sym₁ ⊎-symmetric sym₂ = sym
    where
    sym : Symmetric (_ ⊎-Rel _)
    sym (₁∼₁ x₁∼y₁) = ₁∼₁ (sym₁ x₁∼y₁)
    sym (₂∼₂ x₂∼y₂) = ₂∼₂ (sym₂ x₂∼y₂)
    sym (₁∼₂ ())

  _⊎-transitive_ : {∼₁ : Rel A₁ zero} → Transitive ∼₁ →
                   {∼₂ : Rel A₂ zero} → Transitive ∼₂ →
                   ∀ {P} → Transitive (⊎ʳ P ∼₁ ∼₂)
  trans₁ ⊎-transitive trans₂ = trans
    where
    trans : Transitive (⊎ʳ _ _ _)
    trans (₁∼₁ x∼y) (₁∼₁ y∼z) = ₁∼₁ (trans₁ x∼y y∼z)
    trans (₂∼₂ x∼y) (₂∼₂ y∼z) = ₂∼₂ (trans₂ x∼y y∼z)
    trans (₁∼₂ p)   (₂∼₂ _)     = ₁∼₂ p
    trans (₁∼₁ _)   (₁∼₂ p)     = ₁∼₂ p

  _⊎-antisymmetric_ : {≈₁ ≤₁ : Rel A₁ zero} → Antisymmetric ≈₁ ≤₁ →
                      {≈₂ ≤₂ : Rel A₂ zero} → Antisymmetric ≈₂ ≤₂ →
                      ∀ {P} → Antisymmetric (≈₁ ⊎-Rel ≈₂) (⊎ʳ P ≤₁ ≤₂)
  antisym₁ ⊎-antisymmetric antisym₂ = antisym
    where
    antisym : Antisymmetric (_ ⊎-Rel _) (⊎ʳ _ _ _)
    antisym (₁∼₁ x≤y) (₁∼₁ y≤x) = ₁∼₁ (antisym₁ x≤y y≤x)
    antisym (₂∼₂ x≤y) (₂∼₂ y≤x) = ₂∼₂ (antisym₂ x≤y y≤x)
    antisym (₁∼₂ _)   ()

  _⊎-asymmetric_ : {<₁ : Rel A₁ zero} → Asymmetric <₁ →
                   {<₂ : Rel A₂ zero} → Asymmetric <₂ →
                   ∀ {P} → Asymmetric (⊎ʳ P <₁ <₂)
  asym₁ ⊎-asymmetric asym₂ = asym
    where
    asym : Asymmetric (⊎ʳ _ _ _)
    asym (₁∼₁ x<y) (₁∼₁ y<x) = asym₁ x<y y<x
    asym (₂∼₂ x<y) (₂∼₂ y<x) = asym₂ x<y y<x
    asym (₁∼₂ _)   ()

  _⊎-≈-respects₂_ : {≈₁ ∼₁ : Rel A₁ zero} → ∼₁ Respects₂ ≈₁ →
                    {≈₂ ∼₂ : Rel A₂ zero} → ∼₂ Respects₂ ≈₂ →
                    ∀ {P} → (⊎ʳ P ∼₁ ∼₂) Respects₂ (≈₁ ⊎-Rel ≈₂)
  _⊎-≈-respects₂_ {≈₁ = ≈₁} {∼₁ = ∼₁} resp₁
                  {≈₂ = ≈₂} {∼₂ = ∼₂} resp₂ {P} =
    (λ {_ _ _} → resp¹) ,
    (λ {_ _ _} → resp²)
    where
    resp¹ : ∀ {x} → ((⊎ʳ P ∼₁ ∼₂) x) Respects (≈₁ ⊎-Rel ≈₂)
    resp¹ (₁∼₁ y≈y') (₁∼₁ x∼y) = ₁∼₁ (proj₁ resp₁ y≈y' x∼y)
    resp¹ (₂∼₂ y≈y') (₂∼₂ x∼y) = ₂∼₂ (proj₁ resp₂ y≈y' x∼y)
    resp¹ (₂∼₂ y≈y') (₁∼₂ p)   = (₁∼₂ p)
    resp¹ (₁∼₂ ())   _

    resp² :  ∀ {y}
          → (flip (⊎ʳ P ∼₁ ∼₂) y) Respects (≈₁ ⊎-Rel ≈₂)
    resp² (₁∼₁ x≈x') (₁∼₁ x∼y) = ₁∼₁ (proj₂ resp₁ x≈x' x∼y)
    resp² (₂∼₂ x≈x') (₂∼₂ x∼y) = ₂∼₂ (proj₂ resp₂ x≈x' x∼y)
    resp² (₁∼₁ x≈x') (₁∼₂ p)   = (₁∼₂ p)
    resp² (₁∼₂ ())   _

  _⊎-substitutive_ : {∼₁ : Rel A₁ zero} → Substitutive ∼₁ zero →
                     {∼₂ : Rel A₂ zero} → Substitutive ∼₂ zero →
                     Substitutive (∼₁ ⊎-Rel ∼₂) zero
  subst₁ ⊎-substitutive subst₂ = subst
    where
    subst : Substitutive (_ ⊎-Rel _) zero
    subst P (₁∼₁ x∼y) Px = subst₁ (λ z → P (inj₁ z)) x∼y Px
    subst P (₂∼₂ x∼y) Px = subst₂ (λ z → P (inj₂ z)) x∼y Px
    subst P (₁∼₂ ())  Px

  ⊎-decidable : {∼₁ : Rel A₁ zero} → Decidable ∼₁ →
                {∼₂ : Rel A₂ zero} → Decidable ∼₂ →
                ∀ {P} → (∀ {x y} → Dec (inj₁ x ⟨ ⊎ʳ P ∼₁ ∼₂ ⟩ inj₂ y)) →
                Decidable (⊎ʳ P ∼₁ ∼₂)
  ⊎-decidable {∼₁ = ∼₁} dec₁ {∼₂ = ∼₂} dec₂ {P} dec₁₂ = dec
    where
    dec : Decidable (⊎ʳ P ∼₁ ∼₂)
    dec (inj₁ x) (inj₁ y) with dec₁ x y
    ...                   | yes x∼y = yes (₁∼₁ x∼y)
    ...                   | no  x≁y = no (x≁y ∘ drop-inj₁)
    dec (inj₂ x) (inj₂ y) with dec₂ x y
    ...                   | yes x∼y = yes (₂∼₂ x∼y)
    ...                   | no  x≁y = no (x≁y ∘ drop-inj₂)
    dec (inj₁ x) (inj₂ y) = dec₁₂
    dec (inj₂ x) (inj₁ y) = no (λ())

  _⊎-<-total_ : {≤₁ : Rel A₁ zero} → Total ≤₁ →
                {≤₂ : Rel A₂ zero} → Total ≤₂ →
                Total (≤₁ ⊎-< ≤₂)
  total₁ ⊎-<-total total₂ = total
    where
    total : Total (_ ⊎-< _)
    total (inj₁ x) (inj₁ y) = Sum.map ₁∼₁ ₁∼₁ $ total₁ x y
    total (inj₂ x) (inj₂ y) = Sum.map ₂∼₂ ₂∼₂ $ total₂ x y
    total (inj₁ x) (inj₂ y) = inj₁ (₁∼₂ _)
    total (inj₂ x) (inj₁ y) = inj₂ (₁∼₂ _)

  _⊎-<-trichotomous_ : {≈₁ <₁ : Rel A₁ zero} → Trichotomous ≈₁ <₁ →
                       {≈₂ <₂ : Rel A₂ zero} → Trichotomous ≈₂ <₂ →
                       Trichotomous (≈₁ ⊎-Rel ≈₂) (<₁ ⊎-< <₂)
  _⊎-<-trichotomous_ {≈₁ = ≈₁} {<₁ = <₁} tri₁
                     {≈₂ = ≈₂} {<₂ = <₂} tri₂ = tri
    where
    tri : Trichotomous (≈₁ ⊎-Rel ≈₂) (<₁ ⊎-< <₂)
    tri (inj₁ x) (inj₂ y) = tri< (₁∼₂ _) ₁≁₂ (λ())
    tri (inj₂ x) (inj₁ y) = tri> (λ()) (λ()) (₁∼₂ _)
    tri (inj₁ x) (inj₁ y) with tri₁ x y
    ...                   | tri< x<y x≉y x≯y =
      tri< (₁∼₁ x<y)        (x≉y ∘ drop-inj₁) (x≯y ∘ drop-inj₁)
    ...                   | tri≈ x≮y x≈y x≯y =
      tri≈ (x≮y ∘ drop-inj₁) (₁∼₁ x≈y)    (x≯y ∘ drop-inj₁)
    ...                   | tri> x≮y x≉y x>y =
      tri> (x≮y ∘ drop-inj₁) (x≉y ∘ drop-inj₁) (₁∼₁ x>y)
    tri (inj₂ x) (inj₂ y) with tri₂ x y
    ...                   | tri< x<y x≉y x≯y =
      tri< (₂∼₂ x<y)        (x≉y ∘ drop-inj₂) (x≯y ∘ drop-inj₂)
    ...                   | tri≈ x≮y x≈y x≯y =
      tri≈ (x≮y ∘ drop-inj₂) (₂∼₂ x≈y)    (x≯y ∘ drop-inj₂)
    ...                   | tri> x≮y x≉y x>y =
      tri> (x≮y ∘ drop-inj₂) (x≉y ∘ drop-inj₂) (₂∼₂ x>y)

  ----------------------------------------------------------------------
  -- Some collections of properties which are preserved

  _⊎-isEquivalence_ : {≈₁ : Rel A₁ zero} → IsEquivalence ≈₁ →
                      {≈₂ : Rel A₂ zero} → IsEquivalence ≈₂ →
                      IsEquivalence (≈₁ ⊎-Rel ≈₂)
  eq₁ ⊎-isEquivalence eq₂ = record
    { refl  = refl  eq₁ ⊎-refl        refl  eq₂
    ; sym   = sym   eq₁ ⊎-symmetric   sym   eq₂
    ; trans = trans eq₁ ⊎-transitive  trans eq₂
    }
    where open IsEquivalence

  _⊎-isPreorder_ : {≈₁ ∼₁ : Rel A₁ zero} → IsPreorder ≈₁ ∼₁ →
                   {≈₂ ∼₂ : Rel A₂ zero} → IsPreorder ≈₂ ∼₂ →
                   ∀ {P} → IsPreorder (≈₁ ⊎-Rel ≈₂) (⊎ʳ P ∼₁ ∼₂)
  pre₁ ⊎-isPreorder pre₂ = record
    { isEquivalence = isEquivalence pre₁ ⊎-isEquivalence
                      isEquivalence pre₂
    ; reflexive     = reflexive pre₁ ⊎-reflexive   reflexive pre₂
    ; trans         = trans     pre₁ ⊎-transitive  trans     pre₂
    }
    where open IsPreorder

  _⊎-isDecEquivalence_ : {≈₁ : Rel A₁ zero} → IsDecEquivalence ≈₁ →
                         {≈₂ : Rel A₂ zero} → IsDecEquivalence ≈₂ →
                         IsDecEquivalence (≈₁ ⊎-Rel ≈₂)
  eq₁ ⊎-isDecEquivalence eq₂ = record
    { isEquivalence = isEquivalence eq₁ ⊎-isEquivalence
                      isEquivalence eq₂
    ; _≟_           = ⊎-decidable (_≟_ eq₁) (_≟_ eq₂) (no ₁≁₂)
    }
    where open IsDecEquivalence

  _⊎-isPartialOrder_ : {≈₁ ≤₁ : Rel A₁ zero} → IsPartialOrder ≈₁ ≤₁ →
                       {≈₂ ≤₂ : Rel A₂ zero} → IsPartialOrder ≈₂ ≤₂ →
                       ∀ {P} → IsPartialOrder (≈₁ ⊎-Rel ≈₂) (⊎ʳ P ≤₁ ≤₂)
  po₁ ⊎-isPartialOrder po₂ = record
    { isPreorder = isPreorder po₁ ⊎-isPreorder    isPreorder po₂
    ; antisym    = antisym    po₁ ⊎-antisymmetric antisym    po₂
    }
    where open IsPartialOrder

  _⊎-isStrictPartialOrder_ :
    {≈₁ <₁ : Rel A₁ zero} → IsStrictPartialOrder ≈₁ <₁ →
    {≈₂ <₂ : Rel A₂ zero} → IsStrictPartialOrder ≈₂ <₂ →
    ∀ {P} → IsStrictPartialOrder (≈₁ ⊎-Rel ≈₂) (⊎ʳ P <₁ <₂)
  spo₁ ⊎-isStrictPartialOrder spo₂ = record
    { isEquivalence = isEquivalence spo₁ ⊎-isEquivalence
                      isEquivalence spo₂
    ; irrefl        = irrefl   spo₁ ⊎-irreflexive irrefl   spo₂
    ; trans         = trans    spo₁ ⊎-transitive  trans    spo₂
    ; <-resp-≈      = <-resp-≈ spo₁ ⊎-≈-respects₂ <-resp-≈ spo₂
    }
    where open IsStrictPartialOrder

  _⊎-<-isTotalOrder_ : {≈₁ ≤₁ : Rel A₁ zero} → IsTotalOrder ≈₁ ≤₁ →
                       {≈₂ ≤₂ : Rel A₂ zero} → IsTotalOrder ≈₂ ≤₂ →
                       IsTotalOrder (≈₁ ⊎-Rel ≈₂) (≤₁ ⊎-< ≤₂)
  to₁ ⊎-<-isTotalOrder to₂ = record
    { isPartialOrder = isPartialOrder to₁ ⊎-isPartialOrder
                       isPartialOrder to₂
    ; total          = total to₁ ⊎-<-total total to₂
    }
    where open IsTotalOrder

  _⊎-<-isDecTotalOrder_ :
    {≈₁ ≤₁ : Rel A₁ zero} → IsDecTotalOrder ≈₁ ≤₁ →
    {≈₂ ≤₂ : Rel A₂ zero} → IsDecTotalOrder ≈₂ ≤₂ →
    IsDecTotalOrder (≈₁ ⊎-Rel ≈₂) (≤₁ ⊎-< ≤₂)
  to₁ ⊎-<-isDecTotalOrder to₂ = record
    { isTotalOrder = isTotalOrder to₁ ⊎-<-isTotalOrder isTotalOrder to₂
    ; _≟_          = ⊎-decidable (_≟_  to₁) (_≟_  to₂) (no ₁≁₂)
    ; _≤?_         = ⊎-decidable (_≤?_ to₁) (_≤?_ to₂) (yes (₁∼₂ _))
    }
    where open IsDecTotalOrder

open Dummy public

------------------------------------------------------------------------
-- The game can be taken even further...

_⊎-setoid_ : Setoid _ _ → Setoid _ _ → Setoid _ _
s₁ ⊎-setoid s₂ = record
  { isEquivalence = isEquivalence s₁ ⊎-isEquivalence isEquivalence s₂
  } where open Setoid

_⊎-preorder_ : Preorder _ _ _ → Preorder _ _ _ → Preorder _ _ _
p₁ ⊎-preorder p₂ = record
  { _∼_          = _∼_        p₁ ⊎-Rel        _∼_        p₂
  ; isPreorder   = isPreorder p₁ ⊎-isPreorder isPreorder p₂
  } where open Preorder

_⊎-decSetoid_ : DecSetoid _ _ → DecSetoid _ _ → DecSetoid _ _
ds₁ ⊎-decSetoid ds₂ = record
  { isDecEquivalence = isDecEquivalence ds₁ ⊎-isDecEquivalence
                       isDecEquivalence ds₂
  } where open DecSetoid

_⊎-poset_ : Poset _ _ _ → Poset _ _ _ → Poset _ _ _
po₁ ⊎-poset po₂ = record
  { _≤_            = _≤_ po₁ ⊎-Rel _≤_ po₂
  ; isPartialOrder = isPartialOrder po₁ ⊎-isPartialOrder
                     isPartialOrder po₂
  } where open Poset

_⊎-<-poset_ : Poset _ _ _ → Poset _ _ _ → Poset _ _ _
po₁ ⊎-<-poset po₂ = record
  { _≤_            = _≤_ po₁ ⊎-< _≤_ po₂
  ; isPartialOrder = isPartialOrder po₁ ⊎-isPartialOrder
                     isPartialOrder po₂
  } where open Poset

_⊎-<-strictPartialOrder_ :
  StrictPartialOrder _ _ _ → StrictPartialOrder _ _ _ →
  StrictPartialOrder _ _ _
spo₁ ⊎-<-strictPartialOrder spo₂ = record
  { _<_                  = _<_ spo₁ ⊎-< _<_ spo₂
  ; isStrictPartialOrder = isStrictPartialOrder spo₁
                             ⊎-isStrictPartialOrder
                           isStrictPartialOrder spo₂
  } where open StrictPartialOrder

_⊎-<-totalOrder_ :
  TotalOrder _ _ _ → TotalOrder _ _ _ → TotalOrder _ _ _
to₁ ⊎-<-totalOrder to₂ = record
  { isTotalOrder = isTotalOrder to₁ ⊎-<-isTotalOrder isTotalOrder to₂
  } where open TotalOrder

_⊎-<-decTotalOrder_ :
  DecTotalOrder _ _ _ → DecTotalOrder _ _ _ → DecTotalOrder _ _ _
to₁ ⊎-<-decTotalOrder to₂ = record
  { isDecTotalOrder = isDecTotalOrder to₁ ⊎-<-isDecTotalOrder
                      isDecTotalOrder to₂
  } where open DecTotalOrder

------------------------------------------------------------------------
-- Some properties related to equivalences and inverses

⊎-Rel⇿≡ : {A B : Set} →
          Inverse (P.setoid A ⊎-setoid P.setoid B) (P.setoid (A ⊎ B))
⊎-Rel⇿≡ = record
  { to         = record { _⟨$⟩_ = id; cong = to-cong   }
  ; from       = record { _⟨$⟩_ = id; cong = from-cong }
  ; inverse-of = record
    { left-inverse-of  = λ _ → P.refl ⊎-refl P.refl
    ; right-inverse-of = λ _ → P.refl
    }
  }
  where
  to-cong : (P._≡_ ⊎-Rel P._≡_) ⇒ P._≡_
  to-cong (₁∼₂ ())
  to-cong (₁∼₁ P.refl) = P.refl
  to-cong (₂∼₂ P.refl) = P.refl

  from-cong : P._≡_ ⇒ (P._≡_ ⊎-Rel P._≡_)
  from-cong P.refl = P.refl ⊎-refl P.refl

_⊎-equivalent_ :
  {A B C D : Setoid zero zero} →
  Equivalent A B → Equivalent C D →
  Equivalent (A ⊎-setoid C) (B ⊎-setoid D)
_⊎-equivalent_ {A} {B} {C} {D} A⇔B C⇔D = record
  { to   = record { _⟨$⟩_ = to;   cong = to-cong   }
  ; from = record { _⟨$⟩_ = from; cong = from-cong }
  }
  where
  open Setoid (A ⊎-setoid C) using () renaming (_≈_ to _≈AC_)
  open Setoid (B ⊎-setoid D) using () renaming (_≈_ to _≈BD_)

  to = Sum.map (_⟨$⟩_ (Equivalent.to A⇔B))
               (_⟨$⟩_ (Equivalent.to C⇔D))

  to-cong : _≈AC_ =[ to ]⇒ _≈BD_
  to-cong (₁∼₂ ())
  to-cong (₁∼₁ x∼₁y) = ₁∼₁ $ F.cong (Equivalent.to A⇔B) x∼₁y
  to-cong (₂∼₂ x∼₂y) = ₂∼₂ $ F.cong (Equivalent.to C⇔D) x∼₂y

  from = Sum.map (_⟨$⟩_ (Equivalent.from A⇔B))
                 (_⟨$⟩_ (Equivalent.from C⇔D))

  from-cong : _≈BD_ =[ from ]⇒ _≈AC_
  from-cong (₁∼₂ ())
  from-cong (₁∼₁ x∼₁y) = ₁∼₁ $ F.cong (Equivalent.from A⇔B) x∼₁y
  from-cong (₂∼₂ x∼₂y) = ₂∼₂ $ F.cong (Equivalent.from C⇔D) x∼₂y

_⊎-⇔_ : {A B C D : Set} → A ⇔ B → C ⇔ D → (A ⊎ C) ⇔ (B ⊎ D)
A⇔B ⊎-⇔ C⇔D =
  Inverse.equivalent ⊎-Rel⇿≡ ⟨∘⟩
  A⇔B ⊎-equivalent C⇔D ⟨∘⟩
  Eq.sym (Inverse.equivalent ⊎-Rel⇿≡)

_⊎-inverse_ :
  {A B C D : Setoid zero zero} →
  Inverse A B → Inverse C D → Inverse (A ⊎-setoid C) (B ⊎-setoid D)
A⇿B ⊎-inverse C⇿D = record
  { to         = Equivalent.to   eq
  ; from       = Equivalent.from eq
  ; inverse-of = record
    { left-inverse-of  = [ ₁∼₁ ∘ left-inverse-of A⇿B
                         , ₂∼₂ ∘ left-inverse-of C⇿D
                         ]
    ; right-inverse-of = [ ₁∼₁ ∘ right-inverse-of A⇿B
                         , ₂∼₂ ∘ right-inverse-of C⇿D
                         ]
    }
  }
  where
  open Inverse
  eq = equivalent A⇿B ⊎-equivalent equivalent C⇿D

_⊎-⇿_ : {A B C D : Set} → A ⇿ B → C ⇿ D → (A ⊎ C) ⇿ (B ⊎ D)
A⇿B ⊎-⇿ C⇿D = ⊎-Rel⇿≡ ⟪∘⟫ A⇿B ⊎-inverse C⇿D ⟪∘⟫ Inv.sym ⊎-Rel⇿≡
