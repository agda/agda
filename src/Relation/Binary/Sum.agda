------------------------------------------------------------------------
-- The Agda standard library
--
-- Sums of binary relations
------------------------------------------------------------------------

module Relation.Binary.Sum where

open import Data.Sum as Sum
open import Data.Product
open import Data.Unit.Minimal using (⊤)
open import Data.Empty
open import Function
open import Function.Equality as F using (_⟶_; _⟨$⟩_)
open import Function.Equivalence as Eq
  using (Equivalence; _⇔_; module Equivalence)
open import Function.Injection as Inj
  using (Injection; _↣_; module Injection)
open import Function.Inverse as Inv
  using (Inverse; _↔_; module Inverse)
open import Function.LeftInverse as LeftInv
  using (LeftInverse; _↞_; module LeftInverse)
open import Function.Related
open import Function.Surjection as Surj
  using (Surjection; _↠_; module Surjection)
open import Level
open import Relation.Nullary
import Relation.Nullary.Decidable as Dec
open import Relation.Binary
open import Relation.Binary.PropositionalEquality as P using (_≡_)

module _ {a₁ a₂} {A₁ : Set a₁} {A₂ : Set a₂} where

  ----------------------------------------------------------------------
  -- Sums of relations

  infixr 1 _⊎-Rel_ _⊎-<_

  -- Generalised sum.

  data ⊎ʳ {ℓ₁ ℓ₂} (P : Set) (_∼₁_ : Rel A₁ ℓ₁) (_∼₂_ : Rel A₂ ℓ₂) :
          A₁ ⊎ A₂ → A₁ ⊎ A₂ → Set (a₁ ⊔ a₂ ⊔ ℓ₁ ⊔ ℓ₂) where
    ₁∼₂ : ∀ {x y} (p : P)         → ⊎ʳ P _∼₁_ _∼₂_ (inj₁ x) (inj₂ y)
    ₁∼₁ : ∀ {x y} (x∼₁y : x ∼₁ y) → ⊎ʳ P _∼₁_ _∼₂_ (inj₁ x) (inj₁ y)
    ₂∼₂ : ∀ {x y} (x∼₂y : x ∼₂ y) → ⊎ʳ P _∼₁_ _∼₂_ (inj₂ x) (inj₂ y)

  -- Pointwise sum.

  _⊎-Rel_ : ∀ {ℓ₁ ℓ₂} → Rel A₁ ℓ₁ → Rel A₂ ℓ₂ → Rel (A₁ ⊎ A₂) _
  _⊎-Rel_ = ⊎ʳ ⊥

  -- All things to the left are "smaller than" all things to the
  -- right.

  _⊎-<_ : ∀ {ℓ₁ ℓ₂} → Rel A₁ ℓ₁ → Rel A₂ ℓ₂ → Rel (A₁ ⊎ A₂) _
  _⊎-<_ = ⊎ʳ ⊤

  ----------------------------------------------------------------------
  -- Helpers

  private

    ₁≁₂ : ∀ {ℓ₁ ℓ₂} {∼₁ : Rel A₁ ℓ₁} {∼₂ : Rel A₂ ℓ₂} →
          ∀ {x y} → ¬ (inj₁ x ⟨ ∼₁ ⊎-Rel ∼₂ ⟩ inj₂ y)
    ₁≁₂ (₁∼₂ ())

    drop-inj₁ : ∀ {ℓ₁ ℓ₂} {∼₁ : Rel A₁ ℓ₁} {∼₂ : Rel A₂ ℓ₂} →
                ∀ {P x y} → inj₁ x ⟨ ⊎ʳ P ∼₁ ∼₂ ⟩ inj₁ y → ∼₁ x y
    drop-inj₁ (₁∼₁ x∼y) = x∼y

    drop-inj₂ : ∀ {ℓ₁ ℓ₂} {∼₁ : Rel A₁ ℓ₁} {∼₂ : Rel A₂ ℓ₂} →
                ∀ {P x y} → inj₂ x ⟨ ⊎ʳ P ∼₁ ∼₂ ⟩ inj₂ y → ∼₂ x y
    drop-inj₂ (₂∼₂ x∼y) = x∼y

  ----------------------------------------------------------------------
  -- Some properties which are preserved by the relation formers above

  _⊎-reflexive_ : ∀ {ℓ₁ ℓ₁′} {≈₁ : Rel A₁ ℓ₁} {∼₁ : Rel A₁ ℓ₁′}
                    {ℓ₂ ℓ₂′} {≈₂ : Rel A₂ ℓ₂} {∼₂ : Rel A₂ ℓ₂′} →
                  ≈₁ ⇒ ∼₁ → ≈₂ ⇒ ∼₂ →
                  ∀ {P} → (≈₁ ⊎-Rel ≈₂) ⇒ (⊎ʳ P ∼₁ ∼₂)
  refl₁ ⊎-reflexive refl₂ = refl
    where
    refl : (_ ⊎-Rel _) ⇒ (⊎ʳ _ _ _)
    refl (₁∼₁ x₁≈y₁) = ₁∼₁ (refl₁ x₁≈y₁)
    refl (₂∼₂ x₂≈y₂) = ₂∼₂ (refl₂ x₂≈y₂)
    refl (₁∼₂ ())

  _⊎-refl_ : ∀ {ℓ₁ ℓ₂} {∼₁ : Rel A₁ ℓ₁} {∼₂ : Rel A₂ ℓ₂} →
             Reflexive ∼₁ → Reflexive ∼₂ → Reflexive (∼₁ ⊎-Rel ∼₂)
  refl₁ ⊎-refl refl₂ = refl
    where
    refl : Reflexive (_ ⊎-Rel _)
    refl {x = inj₁ _} = ₁∼₁ refl₁
    refl {x = inj₂ _} = ₂∼₂ refl₂

  _⊎-irreflexive_ : ∀ {ℓ₁ ℓ₁′} {≈₁ : Rel A₁ ℓ₁} {<₁ : Rel A₁ ℓ₁′}
                      {ℓ₂ ℓ₂′} {≈₂ : Rel A₂ ℓ₂} {<₂ : Rel A₂ ℓ₂′} →
                    Irreflexive ≈₁ <₁ → Irreflexive ≈₂ <₂ →
                    ∀ {P} → Irreflexive (≈₁ ⊎-Rel ≈₂) (⊎ʳ P <₁ <₂)
  irrefl₁ ⊎-irreflexive irrefl₂ = irrefl
    where
    irrefl : Irreflexive (_ ⊎-Rel _) (⊎ʳ _ _ _)
    irrefl (₁∼₁ x₁≈y₁) (₁∼₁ x₁<y₁) = irrefl₁ x₁≈y₁ x₁<y₁
    irrefl (₂∼₂ x₂≈y₂) (₂∼₂ x₂<y₂) = irrefl₂ x₂≈y₂ x₂<y₂
    irrefl (₁∼₂ ())    _

  _⊎-symmetric_ : ∀ {ℓ₁ ℓ₂} {∼₁ : Rel A₁ ℓ₁} {∼₂ : Rel A₂ ℓ₂} →
                  Symmetric ∼₁ → Symmetric ∼₂ → Symmetric (∼₁ ⊎-Rel ∼₂)
  sym₁ ⊎-symmetric sym₂ = sym
    where
    sym : Symmetric (_ ⊎-Rel _)
    sym (₁∼₁ x₁∼y₁) = ₁∼₁ (sym₁ x₁∼y₁)
    sym (₂∼₂ x₂∼y₂) = ₂∼₂ (sym₂ x₂∼y₂)
    sym (₁∼₂ ())

  _⊎-transitive_ : ∀ {ℓ₁ ℓ₂} {∼₁ : Rel A₁ ℓ₁} {∼₂ : Rel A₂ ℓ₂} →
                   Transitive ∼₁ → Transitive ∼₂ →
                   ∀ {P} → Transitive (⊎ʳ P ∼₁ ∼₂)
  trans₁ ⊎-transitive trans₂ = trans
    where
    trans : Transitive (⊎ʳ _ _ _)
    trans (₁∼₁ x∼y) (₁∼₁ y∼z) = ₁∼₁ (trans₁ x∼y y∼z)
    trans (₂∼₂ x∼y) (₂∼₂ y∼z) = ₂∼₂ (trans₂ x∼y y∼z)
    trans (₁∼₂ p)   (₂∼₂ _)     = ₁∼₂ p
    trans (₁∼₁ _)   (₁∼₂ p)     = ₁∼₂ p

  _⊎-antisymmetric_ : ∀ {ℓ₁ ℓ₁′} {≈₁ : Rel A₁ ℓ₁} {≤₁ : Rel A₁ ℓ₁′}
                        {ℓ₂ ℓ₂′} {≈₂ : Rel A₂ ℓ₂} {≤₂ : Rel A₂ ℓ₂′} →
                      Antisymmetric ≈₁ ≤₁ → Antisymmetric ≈₂ ≤₂ →
                      ∀ {P} → Antisymmetric (≈₁ ⊎-Rel ≈₂) (⊎ʳ P ≤₁ ≤₂)
  antisym₁ ⊎-antisymmetric antisym₂ = antisym
    where
    antisym : Antisymmetric (_ ⊎-Rel _) (⊎ʳ _ _ _)
    antisym (₁∼₁ x≤y) (₁∼₁ y≤x) = ₁∼₁ (antisym₁ x≤y y≤x)
    antisym (₂∼₂ x≤y) (₂∼₂ y≤x) = ₂∼₂ (antisym₂ x≤y y≤x)
    antisym (₁∼₂ _)   ()

  _⊎-asymmetric_ : ∀ {ℓ₁ ℓ₂} {<₁ : Rel A₁ ℓ₁} {<₂ : Rel A₂ ℓ₂} →
                   Asymmetric <₁ → Asymmetric <₂ →
                   ∀ {P} → Asymmetric (⊎ʳ P <₁ <₂)
  asym₁ ⊎-asymmetric asym₂ = asym
    where
    asym : Asymmetric (⊎ʳ _ _ _)
    asym (₁∼₁ x<y) (₁∼₁ y<x) = asym₁ x<y y<x
    asym (₂∼₂ x<y) (₂∼₂ y<x) = asym₂ x<y y<x
    asym (₁∼₂ _)   ()

  _⊎-≈-respects₂_ : ∀ {ℓ₁ ℓ₁′} {≈₁ : Rel A₁ ℓ₁} {∼₁ : Rel A₁ ℓ₁′}
                      {ℓ₂ ℓ₂′} {≈₂ : Rel A₂ ℓ₂} {∼₂ : Rel A₂ ℓ₂′} →
                    ∼₁ Respects₂ ≈₁ → ∼₂ Respects₂ ≈₂ →
                    ∀ {P} → (⊎ʳ P ∼₁ ∼₂) Respects₂ (≈₁ ⊎-Rel ≈₂)
  _⊎-≈-respects₂_ {≈₁ = ≈₁} {∼₁ = ∼₁}{≈₂ = ≈₂} {∼₂ = ∼₂}
                  resp₁ resp₂ {P} =
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

  _⊎-substitutive_ : ∀ {ℓ₁ ℓ₂ ℓ₃} {∼₁ : Rel A₁ ℓ₁} {∼₂ : Rel A₂ ℓ₂} →
                     Substitutive ∼₁ ℓ₃ → Substitutive ∼₂ ℓ₃ →
                     Substitutive (∼₁ ⊎-Rel ∼₂) ℓ₃
  subst₁ ⊎-substitutive subst₂ = subst
    where
    subst : Substitutive (_ ⊎-Rel _) _
    subst P (₁∼₁ x∼y) Px = subst₁ (λ z → P (inj₁ z)) x∼y Px
    subst P (₂∼₂ x∼y) Px = subst₂ (λ z → P (inj₂ z)) x∼y Px
    subst P (₁∼₂ ())  Px

  ⊎-decidable : ∀ {ℓ₁ ℓ₂} {∼₁ : Rel A₁ ℓ₁} {∼₂ : Rel A₂ ℓ₂} →
                Decidable ∼₁ → Decidable ∼₂ →
                ∀ {P} → (∀ {x y} → Dec (inj₁ x ⟨ ⊎ʳ P ∼₁ ∼₂ ⟩ inj₂ y)) →
                Decidable (⊎ʳ P ∼₁ ∼₂)
  ⊎-decidable {∼₁ = ∼₁} {∼₂ = ∼₂} dec₁ dec₂ {P} dec₁₂ = dec
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

  _⊎-<-total_ : ∀ {ℓ₁ ℓ₂} {≤₁ : Rel A₁ ℓ₁} {≤₂ : Rel A₂ ℓ₂} →
                Total ≤₁ → Total ≤₂ → Total (≤₁ ⊎-< ≤₂)
  total₁ ⊎-<-total total₂ = total
    where
    total : Total (_ ⊎-< _)
    total (inj₁ x) (inj₁ y) = Sum.map ₁∼₁ ₁∼₁ $ total₁ x y
    total (inj₂ x) (inj₂ y) = Sum.map ₂∼₂ ₂∼₂ $ total₂ x y
    total (inj₁ x) (inj₂ y) = inj₁ (₁∼₂ _)
    total (inj₂ x) (inj₁ y) = inj₂ (₁∼₂ _)

  _⊎-<-trichotomous_ : ∀ {ℓ₁ ℓ₁′} {≈₁ : Rel A₁ ℓ₁} {<₁ : Rel A₁ ℓ₁′}
                         {ℓ₂ ℓ₂′} {≈₂ : Rel A₂ ℓ₂} {<₂ : Rel A₂ ℓ₂′} →
                       Trichotomous ≈₁ <₁ → Trichotomous ≈₂ <₂ →
                       Trichotomous (≈₁ ⊎-Rel ≈₂) (<₁ ⊎-< <₂)
  _⊎-<-trichotomous_ {≈₁ = ≈₁} {<₁ = <₁} {≈₂ = ≈₂} {<₂ = <₂}
                     tri₁ tri₂ = tri
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

  _⊎-isEquivalence_ : ∀ {ℓ₁ ℓ₂} {≈₁ : Rel A₁ ℓ₁} {≈₂ : Rel A₂ ℓ₂} →
                      IsEquivalence ≈₁ → IsEquivalence ≈₂ →
                      IsEquivalence (≈₁ ⊎-Rel ≈₂)
  eq₁ ⊎-isEquivalence eq₂ = record
    { refl  = refl  eq₁ ⊎-refl        refl  eq₂
    ; sym   = sym   eq₁ ⊎-symmetric   sym   eq₂
    ; trans = trans eq₁ ⊎-transitive  trans eq₂
    }
    where open IsEquivalence

  _⊎-isPreorder_ : ∀ {ℓ₁ ℓ₁′} {≈₁ : Rel A₁ ℓ₁} {∼₁ : Rel A₁ ℓ₁′}
                     {ℓ₂ ℓ₂′} {≈₂ : Rel A₂ ℓ₂} {∼₂ : Rel A₂ ℓ₂′} →
                   IsPreorder ≈₁ ∼₁ → IsPreorder ≈₂ ∼₂ →
                   ∀ {P} → IsPreorder (≈₁ ⊎-Rel ≈₂) (⊎ʳ P ∼₁ ∼₂)
  pre₁ ⊎-isPreorder pre₂ = record
    { isEquivalence = isEquivalence pre₁ ⊎-isEquivalence
                      isEquivalence pre₂
    ; reflexive     = reflexive pre₁ ⊎-reflexive   reflexive pre₂
    ; trans         = trans     pre₁ ⊎-transitive  trans     pre₂
    }
    where open IsPreorder

  _⊎-isDecEquivalence_ : ∀ {ℓ₁ ℓ₂} {≈₁ : Rel A₁ ℓ₁} {≈₂ : Rel A₂ ℓ₂} →
                         IsDecEquivalence ≈₁ → IsDecEquivalence ≈₂ →
                         IsDecEquivalence (≈₁ ⊎-Rel ≈₂)
  eq₁ ⊎-isDecEquivalence eq₂ = record
    { isEquivalence = isEquivalence eq₁ ⊎-isEquivalence
                      isEquivalence eq₂
    ; _≟_           = ⊎-decidable (_≟_ eq₁) (_≟_ eq₂) (no ₁≁₂)
    }
    where open IsDecEquivalence

  _⊎-isPartialOrder_ : ∀ {ℓ₁ ℓ₁′} {≈₁ : Rel A₁ ℓ₁} {≤₁ : Rel A₁ ℓ₁′}
                         {ℓ₂ ℓ₂′} {≈₂ : Rel A₂ ℓ₂} {≤₂ : Rel A₂ ℓ₂′} →
                       IsPartialOrder ≈₁ ≤₁ → IsPartialOrder ≈₂ ≤₂ →
                       ∀ {P} → IsPartialOrder (≈₁ ⊎-Rel ≈₂) (⊎ʳ P ≤₁ ≤₂)
  po₁ ⊎-isPartialOrder po₂ = record
    { isPreorder = isPreorder po₁ ⊎-isPreorder    isPreorder po₂
    ; antisym    = antisym    po₁ ⊎-antisymmetric antisym    po₂
    }
    where open IsPartialOrder

  _⊎-isStrictPartialOrder_ :
    ∀ {ℓ₁ ℓ₁′} {≈₁ : Rel A₁ ℓ₁} {<₁ : Rel A₁ ℓ₁′}
      {ℓ₂ ℓ₂′} {≈₂ : Rel A₂ ℓ₂} {<₂ : Rel A₂ ℓ₂′} →
    IsStrictPartialOrder ≈₁ <₁ → IsStrictPartialOrder ≈₂ <₂ →
    ∀ {P} → IsStrictPartialOrder (≈₁ ⊎-Rel ≈₂) (⊎ʳ P <₁ <₂)
  spo₁ ⊎-isStrictPartialOrder spo₂ = record
    { isEquivalence = isEquivalence spo₁ ⊎-isEquivalence
                      isEquivalence spo₂
    ; irrefl        = irrefl   spo₁ ⊎-irreflexive irrefl   spo₂
    ; trans         = trans    spo₁ ⊎-transitive  trans    spo₂
    ; <-resp-≈      = <-resp-≈ spo₁ ⊎-≈-respects₂ <-resp-≈ spo₂
    }
    where open IsStrictPartialOrder

  _⊎-<-isTotalOrder_ : ∀ {ℓ₁ ℓ₁′} {≈₁ : Rel A₁ ℓ₁} {≤₁ : Rel A₁ ℓ₁′}
                         {ℓ₂ ℓ₂′} {≈₂ : Rel A₂ ℓ₂} {≤₂ : Rel A₂ ℓ₂′} →
                       IsTotalOrder ≈₁ ≤₁ → IsTotalOrder ≈₂ ≤₂ →
                       IsTotalOrder (≈₁ ⊎-Rel ≈₂) (≤₁ ⊎-< ≤₂)
  to₁ ⊎-<-isTotalOrder to₂ = record
    { isPartialOrder = isPartialOrder to₁ ⊎-isPartialOrder
                       isPartialOrder to₂
    ; total          = total to₁ ⊎-<-total total to₂
    }
    where open IsTotalOrder

  _⊎-<-isDecTotalOrder_ :
    ∀ {ℓ₁ ℓ₁′} {≈₁ : Rel A₁ ℓ₁} {≤₁ : Rel A₁ ℓ₁′}
      {ℓ₂ ℓ₂′} {≈₂ : Rel A₂ ℓ₂} {≤₂ : Rel A₂ ℓ₂′} →
    IsDecTotalOrder ≈₁ ≤₁ → IsDecTotalOrder ≈₂ ≤₂ →
    IsDecTotalOrder (≈₁ ⊎-Rel ≈₂) (≤₁ ⊎-< ≤₂)
  to₁ ⊎-<-isDecTotalOrder to₂ = record
    { isTotalOrder = isTotalOrder to₁ ⊎-<-isTotalOrder isTotalOrder to₂
    ; _≟_          = ⊎-decidable (_≟_  to₁) (_≟_  to₂) (no ₁≁₂)
    ; _≤?_         = ⊎-decidable (_≤?_ to₁) (_≤?_ to₂) (yes (₁∼₂ _))
    }
    where open IsDecTotalOrder

  _⊎-<-isStrictTotalOrder_ :
    ∀ {ℓ₁ ℓ₁′} {≈₁ : Rel A₁ ℓ₁} {<₁ : Rel A₁ ℓ₁′}
      {ℓ₂ ℓ₂′} {≈₂ : Rel A₂ ℓ₂} {<₂ : Rel A₂ ℓ₂′} →
    IsStrictTotalOrder ≈₁ <₁ → IsStrictTotalOrder ≈₂ <₂ →
    IsStrictTotalOrder (≈₁ ⊎-Rel ≈₂) (<₁ ⊎-< <₂)
  sto₁ ⊎-<-isStrictTotalOrder sto₂ = record
    { isEquivalence = isEquivalence sto₁ ⊎-isEquivalence
                      isEquivalence sto₂
    ; trans         = trans    sto₁ ⊎-transitive     trans    sto₂
    ; compare       = compare  sto₁ ⊎-<-trichotomous compare  sto₂
    ; <-resp-≈      = <-resp-≈ sto₁ ⊎-≈-respects₂    <-resp-≈ sto₂
    }
    where open IsStrictTotalOrder

------------------------------------------------------------------------
-- The game can be taken even further...

_⊎-setoid_ : ∀ {s₁ s₂ s₃ s₄} →
             Setoid s₁ s₂ → Setoid s₃ s₄ → Setoid _ _
s₁ ⊎-setoid s₂ = record
  { isEquivalence = isEquivalence s₁ ⊎-isEquivalence isEquivalence s₂
  } where open Setoid

_⊎-preorder_ : ∀ {p₁ p₂ p₃ p₄ p₅ p₆} →
               Preorder p₁ p₂ p₃ → Preorder p₄ p₅ p₆ → Preorder _ _ _
p₁ ⊎-preorder p₂ = record
  { _∼_          = _∼_        p₁ ⊎-Rel        _∼_        p₂
  ; isPreorder   = isPreorder p₁ ⊎-isPreorder isPreorder p₂
  } where open Preorder

_⊎-decSetoid_ : ∀ {s₁ s₂ s₃ s₄} →
                DecSetoid s₁ s₂ → DecSetoid s₃ s₄ → DecSetoid _ _
ds₁ ⊎-decSetoid ds₂ = record
  { isDecEquivalence = isDecEquivalence ds₁ ⊎-isDecEquivalence
                       isDecEquivalence ds₂
  } where open DecSetoid

_⊎-poset_ : ∀ {p₁ p₂ p₃ p₄ p₅ p₆} →
            Poset p₁ p₂ p₃ → Poset p₄ p₅ p₆ → Poset _ _ _
po₁ ⊎-poset po₂ = record
  { _≤_            = _≤_ po₁ ⊎-Rel _≤_ po₂
  ; isPartialOrder = isPartialOrder po₁ ⊎-isPartialOrder
                     isPartialOrder po₂
  } where open Poset

_⊎-<-poset_ : ∀ {p₁ p₂ p₃ p₄ p₅ p₆} →
              Poset p₁ p₂ p₃ → Poset p₄ p₅ p₆ → Poset _ _ _
po₁ ⊎-<-poset po₂ = record
  { _≤_            = _≤_ po₁ ⊎-< _≤_ po₂
  ; isPartialOrder = isPartialOrder po₁ ⊎-isPartialOrder
                     isPartialOrder po₂
  } where open Poset

_⊎-<-strictPartialOrder_ :
  ∀ {p₁ p₂ p₃ p₄ p₅ p₆} →
  StrictPartialOrder p₁ p₂ p₃ → StrictPartialOrder p₄ p₅ p₆ →
  StrictPartialOrder _ _ _
spo₁ ⊎-<-strictPartialOrder spo₂ = record
  { _<_                  = _<_ spo₁ ⊎-< _<_ spo₂
  ; isStrictPartialOrder = isStrictPartialOrder spo₁
                             ⊎-isStrictPartialOrder
                           isStrictPartialOrder spo₂
  } where open StrictPartialOrder

_⊎-<-totalOrder_ :
  ∀ {t₁ t₂ t₃ t₄ t₅ t₆} →
  TotalOrder t₁ t₂ t₃ → TotalOrder t₄ t₅ t₆ → TotalOrder _ _ _
to₁ ⊎-<-totalOrder to₂ = record
  { isTotalOrder = isTotalOrder to₁ ⊎-<-isTotalOrder isTotalOrder to₂
  } where open TotalOrder

_⊎-<-decTotalOrder_ :
  ∀ {t₁ t₂ t₃ t₄ t₅ t₆} →
  DecTotalOrder t₁ t₂ t₃ → DecTotalOrder t₄ t₅ t₆ → DecTotalOrder _ _ _
to₁ ⊎-<-decTotalOrder to₂ = record
  { isDecTotalOrder = isDecTotalOrder to₁ ⊎-<-isDecTotalOrder
                      isDecTotalOrder to₂
  } where open DecTotalOrder

_⊎-<-strictTotalOrder_ :
  ∀ {p₁ p₂ p₃ p₄ p₅ p₆} →
  StrictTotalOrder p₁ p₂ p₃ → StrictTotalOrder p₄ p₅ p₆ →
  StrictTotalOrder _ _ _
sto₁ ⊎-<-strictTotalOrder sto₂ = record
  { _<_                = _<_ sto₁ ⊎-< _<_ sto₂
  ; isStrictTotalOrder = isStrictTotalOrder sto₁
                           ⊎-<-isStrictTotalOrder
                         isStrictTotalOrder sto₂
  } where open StrictTotalOrder

------------------------------------------------------------------------
-- Some properties related to "relatedness"

private

  to-cong : ∀ {a b} {A : Set a} {B : Set b} →
            (_≡_ ⊎-Rel _≡_) ⇒ _≡_ {A = A ⊎ B}
  to-cong (₁∼₂ ())
  to-cong (₁∼₁ P.refl) = P.refl
  to-cong (₂∼₂ P.refl) = P.refl

  from-cong : ∀ {a b} {A : Set a} {B : Set b} →
              _≡_ {A = A ⊎ B} ⇒ (_≡_ ⊎-Rel _≡_)
  from-cong P.refl = P.refl ⊎-refl P.refl

⊎-Rel↔≡ : ∀ {a b} (A : Set a) (B : Set b) →
          Inverse (P.setoid A ⊎-setoid P.setoid B) (P.setoid (A ⊎ B))
⊎-Rel↔≡ _ _ = record
  { to         = record { _⟨$⟩_ = id; cong = to-cong   }
  ; from       = record { _⟨$⟩_ = id; cong = from-cong }
  ; inverse-of = record
    { left-inverse-of  = λ _ → P.refl ⊎-refl P.refl
    ; right-inverse-of = λ _ → P.refl
    }
  }

_⊎-≟_ : ∀ {a b} {A : Set a} {B : Set b} →
        Decidable {A = A} _≡_ → Decidable {A = B} _≡_ →
        Decidable {A = A ⊎ B} _≡_
(dec₁ ⊎-≟ dec₂) s₁ s₂ = Dec.map′ to-cong from-cong (s₁ ≟ s₂)
  where
  open DecSetoid (P.decSetoid dec₁ ⊎-decSetoid P.decSetoid dec₂)

_⊎-⟶_ :
  ∀ {s₁ s₂ s₃ s₄ s₅ s₆ s₇ s₈}
    {A : Setoid s₁ s₂} {B : Setoid s₃ s₄}
    {C : Setoid s₅ s₆} {D : Setoid s₇ s₈} →
  A ⟶ B → C ⟶ D → (A ⊎-setoid C) ⟶ (B ⊎-setoid D)
_⊎-⟶_ {A = A} {B} {C} {D} f g = record
  { _⟨$⟩_ = fg
  ; cong  = fg-cong
  }
  where
  open Setoid (A ⊎-setoid C) using () renaming (_≈_ to _≈AC_)
  open Setoid (B ⊎-setoid D) using () renaming (_≈_ to _≈BD_)

  fg = Sum.map (_⟨$⟩_ f) (_⟨$⟩_ g)

  fg-cong : _≈AC_ =[ fg ]⇒ _≈BD_
  fg-cong (₁∼₂ ())
  fg-cong (₁∼₁ x∼₁y) = ₁∼₁ $ F.cong f x∼₁y
  fg-cong (₂∼₂ x∼₂y) = ₂∼₂ $ F.cong g x∼₂y

_⊎-equivalence_ :
  ∀ {s₁ s₂ s₃ s₄ s₅ s₆ s₇ s₈}
    {A : Setoid s₁ s₂} {B : Setoid s₃ s₄}
    {C : Setoid s₅ s₆} {D : Setoid s₇ s₈} →
  Equivalence A B → Equivalence C D →
  Equivalence (A ⊎-setoid C) (B ⊎-setoid D)
A⇔B ⊎-equivalence C⇔D = record
  { to   = to   A⇔B ⊎-⟶ to   C⇔D
  ; from = from A⇔B ⊎-⟶ from C⇔D
  } where open Equivalence

_⊎-⇔_ : ∀ {a b c d} {A : Set a} {B : Set b} {C : Set c} {D : Set d} →
        A ⇔ B → C ⇔ D → (A ⊎ C) ⇔ (B ⊎ D)
_⊎-⇔_ {A = A} {B} {C} {D} A⇔B C⇔D =
  Inverse.equivalence (⊎-Rel↔≡ B D) ⟨∘⟩
  A⇔B ⊎-equivalence C⇔D ⟨∘⟩
  Eq.sym (Inverse.equivalence (⊎-Rel↔≡ A C))
  where open Eq using () renaming (_∘_ to _⟨∘⟩_)

_⊎-injection_ :
  ∀ {s₁ s₂ s₃ s₄ s₅ s₆ s₇ s₈}
    {A : Setoid s₁ s₂} {B : Setoid s₃ s₄}
    {C : Setoid s₅ s₆} {D : Setoid s₇ s₈} →
  Injection A B → Injection C D →
  Injection (A ⊎-setoid C) (B ⊎-setoid D)
_⊎-injection_ {A = A} {B} {C} {D} A↣B C↣D = record
  { to        = to A↣B ⊎-⟶ to C↣D
  ; injective = inj _ _
  }
  where
  open Injection
  open Setoid (A ⊎-setoid C) using () renaming (_≈_ to _≈AC_)
  open Setoid (B ⊎-setoid D) using () renaming (_≈_ to _≈BD_)

  inj : ∀ x y →
        (to A↣B ⊎-⟶ to C↣D) ⟨$⟩ x ≈BD (to A↣B ⊎-⟶ to C↣D) ⟨$⟩ y →
        x ≈AC y
  inj (inj₁ x) (inj₁ y) (₁∼₁ x∼₁y) = ₁∼₁ (injective A↣B x∼₁y)
  inj (inj₂ x) (inj₂ y) (₂∼₂ x∼₂y) = ₂∼₂ (injective C↣D x∼₂y)
  inj (inj₁ x) (inj₂ y) (₁∼₂ ())
  inj (inj₂ x) (inj₁ y) ()

_⊎-↣_ : ∀ {a b c d} {A : Set a} {B : Set b} {C : Set c} {D : Set d} →
        A ↣ B → C ↣ D → (A ⊎ C) ↣ (B ⊎ D)
_⊎-↣_ {A = A} {B} {C} {D} A↣B C↣D =
  Inverse.injection (⊎-Rel↔≡ B D) ⟨∘⟩
  A↣B ⊎-injection C↣D ⟨∘⟩
  Inverse.injection (Inv.sym (⊎-Rel↔≡ A C))
  where open Inj using () renaming (_∘_ to _⟨∘⟩_)

_⊎-left-inverse_ :
  ∀ {s₁ s₂ s₃ s₄ s₅ s₆ s₇ s₈}
    {A : Setoid s₁ s₂} {B : Setoid s₃ s₄}
    {C : Setoid s₅ s₆} {D : Setoid s₇ s₈} →
  LeftInverse A B → LeftInverse C D →
  LeftInverse (A ⊎-setoid C) (B ⊎-setoid D)
A↞B ⊎-left-inverse C↞D = record
  { to              = Equivalence.to eq
  ; from            = Equivalence.from eq
  ; left-inverse-of = [ ₁∼₁ ∘ left-inverse-of A↞B
                      , ₂∼₂ ∘ left-inverse-of C↞D
                      ]
  }
  where
  open LeftInverse
  eq = LeftInverse.equivalence A↞B ⊎-equivalence
       LeftInverse.equivalence C↞D

_⊎-↞_ : ∀ {a b c d} {A : Set a} {B : Set b} {C : Set c} {D : Set d} →
        A ↞ B → C ↞ D → (A ⊎ C) ↞ (B ⊎ D)
_⊎-↞_ {A = A} {B} {C} {D} A↞B C↞D =
  Inverse.left-inverse (⊎-Rel↔≡ B D) ⟨∘⟩
  A↞B ⊎-left-inverse C↞D ⟨∘⟩
  Inverse.left-inverse (Inv.sym (⊎-Rel↔≡ A C))
  where open LeftInv using () renaming (_∘_ to _⟨∘⟩_)

_⊎-surjection_ :
  ∀ {s₁ s₂ s₃ s₄ s₅ s₆ s₇ s₈}
    {A : Setoid s₁ s₂} {B : Setoid s₃ s₄}
    {C : Setoid s₅ s₆} {D : Setoid s₇ s₈} →
  Surjection A B → Surjection C D →
  Surjection (A ⊎-setoid C) (B ⊎-setoid D)
A↠B ⊎-surjection C↠D = record
  { to         = LeftInverse.from inv
  ; surjective = record
    { from             = LeftInverse.to inv
    ; right-inverse-of = LeftInverse.left-inverse-of inv
    }
  }
  where
  open Surjection
  inv = right-inverse A↠B ⊎-left-inverse right-inverse C↠D

_⊎-↠_ : ∀ {a b c d} {A : Set a} {B : Set b} {C : Set c} {D : Set d} →
        A ↠ B → C ↠ D → (A ⊎ C) ↠ (B ⊎ D)
_⊎-↠_ {A = A} {B} {C} {D} A↠B C↠D =
  Inverse.surjection (⊎-Rel↔≡ B D) ⟨∘⟩
  A↠B ⊎-surjection C↠D ⟨∘⟩
  Inverse.surjection (Inv.sym (⊎-Rel↔≡ A C))
  where open Surj using () renaming (_∘_ to _⟨∘⟩_)

_⊎-inverse_ :
  ∀ {s₁ s₂ s₃ s₄ s₅ s₆ s₇ s₈}
    {A : Setoid s₁ s₂} {B : Setoid s₃ s₄}
    {C : Setoid s₅ s₆} {D : Setoid s₇ s₈} →
  Inverse A B → Inverse C D → Inverse (A ⊎-setoid C) (B ⊎-setoid D)
A↔B ⊎-inverse C↔D = record
  { to         = Surjection.to   surj
  ; from       = Surjection.from surj
  ; inverse-of = record
    { left-inverse-of  = LeftInverse.left-inverse-of inv
    ; right-inverse-of = Surjection.right-inverse-of surj
    }
  }
  where
  open Inverse
  surj = Inverse.surjection   A↔B ⊎-surjection
         Inverse.surjection   C↔D
  inv  = Inverse.left-inverse A↔B ⊎-left-inverse
         Inverse.left-inverse C↔D

_⊎-↔_ : ∀ {a b c d} {A : Set a} {B : Set b} {C : Set c} {D : Set d} →
        A ↔ B → C ↔ D → (A ⊎ C) ↔ (B ⊎ D)
_⊎-↔_ {A = A} {B} {C} {D} A↔B C↔D =
  ⊎-Rel↔≡ B D ⟨∘⟩ A↔B ⊎-inverse C↔D ⟨∘⟩ Inv.sym (⊎-Rel↔≡ A C)
  where open Inv using () renaming (_∘_ to _⟨∘⟩_)

_⊎-cong_ : ∀ {k a b c d} {A : Set a} {B : Set b} {C : Set c} {D : Set d} →
           A ∼[ k ] B → C ∼[ k ] D → (A ⊎ C) ∼[ k ] (B ⊎ D)
_⊎-cong_ {implication}         = Sum.map
_⊎-cong_ {reverse-implication} = λ f g → lam (Sum.map (app-← f) (app-← g))
_⊎-cong_ {equivalence}         = _⊎-⇔_
_⊎-cong_ {injection}           = _⊎-↣_
_⊎-cong_ {reverse-injection}   = λ f g → lam (app-↢ f ⊎-↣ app-↢ g)
_⊎-cong_ {left-inverse}        = _⊎-↞_
_⊎-cong_ {surjection}          = _⊎-↠_
_⊎-cong_ {bijection}           = _⊎-↔_
