------------------------------------------------------------------------
-- The Agda standard library
--
-- Sums of binary relations
------------------------------------------------------------------------

module Data.Sum.Relation.LeftOrder where

open import Data.Sum as Sum
import Data.Sum.Relation.Core as Core
open import Data.Sum.Relation.Pointwise as Pointwise using (Pointwise; ₁≁₂)
open import Data.Product
open import Data.Unit.Base using (⊤)
open import Data.Empty
open import Function
open import Level
open import Relation.Nullary
import Relation.Nullary.Decidable as Dec
open import Relation.Binary
open import Relation.Binary.PropositionalEquality as P using (_≡_)

module _ {a₁ a₂} {A₁ : Set a₁} {A₂ : Set a₂} where

  ----------------------------------------------------------------------
  -- Left order

  open Core public using (₁∼₂; ₁∼₁; ₂∼₂)

  infixr 1 _⊎-<_

  _⊎-<_ : ∀ {ℓ₁ ℓ₂} → Rel A₁ ℓ₁ → Rel A₂ ℓ₂ → Rel (A₁ ⊎ A₂) _
  _⊎-<_ = Core.⊎ʳ ⊤

  ----------------------------------------------------------------------
  -- Some properties which are preserved by _⊎-<_

  module _ {ℓ₁ ℓ₂} {∼₁ : Rel A₁ ℓ₁} {∼₂ : Rel A₂ ℓ₂} where

    ⊎-<-refl : Reflexive ∼₁ → Reflexive ∼₂ →
               Reflexive (∼₁ ⊎-< ∼₂)
    ⊎-<-refl refl₁ refl₂ = Core._⊎-refl_ refl₁ refl₂

    ⊎-<-transitive : Transitive ∼₁ → Transitive ∼₂ →
                     Transitive (∼₁ ⊎-< ∼₂)
    ⊎-<-transitive trans₁ trans₂ = Core._⊎-transitive_ trans₁ trans₂

    ⊎-<-asymmetric : Asymmetric ∼₁ → Asymmetric ∼₂ →
                     Asymmetric (∼₁ ⊎-< ∼₂)
    ⊎-<-asymmetric asym₁ asym₂ = asym₁ Core.⊎-asymmetric asym₂

    ⊎-<-total : Total ∼₁ → Total ∼₂ → Total (∼₁ ⊎-< ∼₂)
    ⊎-<-total total₁ total₂ = total
      where
      total : Total (_ ⊎-< _)
      total (inj₁ x) (inj₁ y) = Sum.map ₁∼₁ ₁∼₁ $ total₁ x y
      total (inj₂ x) (inj₂ y) = Sum.map ₂∼₂ ₂∼₂ $ total₂ x y
      total (inj₁ x) (inj₂ y) = inj₁ (₁∼₂ _)
      total (inj₂ x) (inj₁ y) = inj₂ (₁∼₂ _)

    ⊎-<-decidable : Decidable ∼₁ → Decidable ∼₂ →
                  (∀ {x y} → Dec (inj₁ x ⟨ ∼₁ ⊎-< ∼₂ ⟩ inj₂ y)) →
                  Decidable (∼₁ ⊎-< ∼₂)
    ⊎-<-decidable dec₁ dec₂ dec₁₂ = Core.⊎-decidable dec₁ dec₂ dec₁₂


  module _ {ℓ₁ ℓ₂} {∼₁ : Rel A₁ ℓ₁} {≈₁ : Rel A₁ ℓ₂}
           {ℓ₃ ℓ₄} {∼₂ : Rel A₂ ℓ₃} {≈₂ : Rel A₂ ℓ₄} where

    ⊎-<-reflexive : ≈₁ ⇒ ∼₁ → ≈₂ ⇒ ∼₂ →
                    (Pointwise ≈₁ ≈₂) ⇒ (∼₁ ⊎-< ∼₂)
    ⊎-<-reflexive refl₁ refl₂ = refl₁ Core.⊎-reflexive refl₂

    ⊎-<-irreflexive : Irreflexive ≈₁ ∼₁ → Irreflexive ≈₂ ∼₂ →
                      Irreflexive (Pointwise ≈₁ ≈₂) (∼₁ ⊎-< ∼₂)
    ⊎-<-irreflexive irrefl₁ irrefl₂ = irrefl₁ Core.⊎-irreflexive irrefl₂

    ⊎-<-antisymmetric : Antisymmetric ≈₁ ∼₁ → Antisymmetric ≈₂ ∼₂ →
                        Antisymmetric (Pointwise ≈₁ ≈₂) (∼₁ ⊎-< ∼₂)
    ⊎-<-antisymmetric antisym₁ antisym₂ = antisym₁ Core.⊎-antisymmetric antisym₂

    ⊎-<-respects₂ : ∼₁ Respects₂ ≈₁ → ∼₂ Respects₂ ≈₂ →
                    (∼₁ ⊎-< ∼₂) Respects₂ (Pointwise ≈₁ ≈₂)
    ⊎-<-respects₂ resp₁ resp₂ = Core._⊎-≈-respects₂_ resp₁ resp₂

    ⊎-<-trichotomous : Trichotomous ≈₁ ∼₁ → Trichotomous ≈₂ ∼₂ →
                         Trichotomous (Pointwise ≈₁ ≈₂) (∼₁ ⊎-< ∼₂)
    ⊎-<-trichotomous tri₁ tri₂ = tri
      where
      tri : Trichotomous (Pointwise ≈₁ ≈₂) (∼₁ ⊎-< ∼₂)
      tri (inj₁ x) (inj₂ y) = tri< (₁∼₂ _) ₁≁₂ (λ())
      tri (inj₂ x) (inj₁ y) = tri> (λ()) (λ()) (₁∼₂ _)
      tri (inj₁ x) (inj₁ y) with tri₁ x y
      ... | tri< x<y x≉y x≯y =
        tri< (₁∼₁ x<y) (x≉y ∘ Core.drop-inj₁) (x≯y ∘ Core.drop-inj₁)
      ... | tri≈ x≮y x≈y x≯y =
        tri≈ (x≮y ∘ Core.drop-inj₁) (₁∼₁ x≈y) (x≯y ∘ Core.drop-inj₁)
      ... | tri> x≮y x≉y x>y =
        tri> (x≮y ∘ Core.drop-inj₁) (x≉y ∘ Core.drop-inj₁) (₁∼₁ x>y)
      tri (inj₂ x) (inj₂ y) with tri₂ x y
      ... | tri< x<y x≉y x≯y =
        tri< (₂∼₂ x<y) (x≉y ∘ Core.drop-inj₂) (x≯y ∘ Core.drop-inj₂)
      ... | tri≈ x≮y x≈y x≯y =
        tri≈ (x≮y ∘ Core.drop-inj₂) (₂∼₂ x≈y) (x≯y ∘ Core.drop-inj₂)
      ... | tri> x≮y x≉y x>y =
        tri> (x≮y ∘ Core.drop-inj₂) (x≉y ∘ Core.drop-inj₂) (₂∼₂ x>y)

  ----------------------------------------------------------------------
  -- Some collections of properties which are preserved

  module _ {ℓ₁ ℓ₂} {≈₁ : Rel A₁ ℓ₁} {∼₁ : Rel A₁ ℓ₂}
           {ℓ₃ ℓ₄} {≈₂ : Rel A₂ ℓ₃} {∼₂ : Rel A₂ ℓ₄} where

    ⊎-<-isPreorder : IsPreorder ≈₁ ∼₁ → IsPreorder ≈₂ ∼₂ →
                     IsPreorder (Pointwise ≈₁ ≈₂) (∼₁ ⊎-< ∼₂)
    ⊎-<-isPreorder pre₁ pre₂ = record
      { isEquivalence =
          Pointwise.⊎-isEquivalence (isEquivalence pre₁) (isEquivalence pre₂)
      ; reflexive     = ⊎-<-reflexive (reflexive pre₁) (reflexive pre₂)
      ; trans         = ⊎-<-transitive (trans pre₁) (trans pre₂)
      }
      where open IsPreorder

    ⊎-<-isPartialOrder : IsPartialOrder ≈₁ ∼₁ →
                         IsPartialOrder ≈₂ ∼₂ →
                         IsPartialOrder (Pointwise ≈₁ ≈₂) (∼₁ ⊎-< ∼₂)
    ⊎-<-isPartialOrder po₁ po₂ = record
      { isPreorder = ⊎-<-isPreorder (isPreorder po₁) (isPreorder po₂)
      ; antisym    = ⊎-<-antisymmetric (antisym po₁) (antisym    po₂)
      }
      where open IsPartialOrder

    ⊎-<-isStrictPartialOrder : IsStrictPartialOrder ≈₁ ∼₁ →
                               IsStrictPartialOrder ≈₂ ∼₂ →
                               IsStrictPartialOrder (Pointwise ≈₁ ≈₂) (∼₁ ⊎-< ∼₂)
    ⊎-<-isStrictPartialOrder spo₁ spo₂ = record
      { isEquivalence = Pointwise.⊎-isEquivalence (isEquivalence spo₁) (isEquivalence spo₂)
      ; irrefl        = ⊎-<-irreflexive   (irrefl spo₁) (irrefl   spo₂)
      ; trans         = ⊎-<-transitive    (trans spo₁)  (trans    spo₂)
      ; <-resp-≈      = ⊎-<-respects₂   (<-resp-≈ spo₁) (<-resp-≈ spo₂)
      }
      where open IsStrictPartialOrder

    ⊎-<-isTotalOrder : IsTotalOrder ≈₁ ∼₁ →
                       IsTotalOrder ≈₂ ∼₂ →
                       IsTotalOrder (Pointwise ≈₁ ≈₂) (∼₁ ⊎-< ∼₂)
    ⊎-<-isTotalOrder to₁ to₂ = record
      { isPartialOrder = ⊎-<-isPartialOrder (isPartialOrder to₁) (isPartialOrder to₂)
      ; total          = ⊎-<-total (total to₁) (total to₂)
      }
      where open IsTotalOrder

    ⊎-<-isDecTotalOrder : IsDecTotalOrder ≈₁ ∼₁ →
                          IsDecTotalOrder ≈₂ ∼₂ →
                          IsDecTotalOrder (Pointwise ≈₁ ≈₂) (∼₁ ⊎-< ∼₂)
    ⊎-<-isDecTotalOrder to₁ to₂ = record
      { isTotalOrder = ⊎-<-isTotalOrder (isTotalOrder to₁) (isTotalOrder to₂)
      ; _≟_          = Pointwise.⊎-decidable (_≟_  to₁) (_≟_  to₂)
      ; _≤?_         = ⊎-<-decidable (_≤?_ to₁) (_≤?_ to₂) (yes (₁∼₂ _))
      }
      where open IsDecTotalOrder

    ⊎-<-isStrictTotalOrder : IsStrictTotalOrder ≈₁ ∼₁ →
                             IsStrictTotalOrder ≈₂ ∼₂ →
                             IsStrictTotalOrder (Pointwise ≈₁ ≈₂) (∼₁ ⊎-< ∼₂)
    ⊎-<-isStrictTotalOrder sto₁ sto₂ = record
      { isEquivalence = Pointwise.⊎-isEquivalence (isEquivalence sto₁) (isEquivalence sto₂)
      ; trans         = ⊎-<-transitive (trans sto₁) (trans sto₂)
      ; compare       = ⊎-<-trichotomous (compare sto₁) (compare sto₂)
      }
      where open IsStrictTotalOrder

------------------------------------------------------------------------
-- "Packages" can also be combined.

module _ {a b c d e f} where

  ⊎-<-preorder : Preorder a b c →
                 Preorder d e f →
                 Preorder _ _ _
  ⊎-<-preorder p₁ p₂ = record
    { isPreorder   =
        ⊎-<-isPreorder (isPreorder p₁) (isPreorder p₂)
    } where open Preorder

  ⊎-<-poset : Poset a b c →
              Poset a b c →
              Poset _ _ _
  ⊎-<-poset po₁ po₂ = record
    { isPartialOrder =
        ⊎-<-isPartialOrder (isPartialOrder po₁) (isPartialOrder po₂)
    } where open Poset

  ⊎-<-strictPartialOrder : StrictPartialOrder a b c →
                           StrictPartialOrder d e f →
                           StrictPartialOrder _ _ _
  ⊎-<-strictPartialOrder spo₁ spo₂ = record
    { isStrictPartialOrder =
      ⊎-<-isStrictPartialOrder (isStrictPartialOrder spo₁) (isStrictPartialOrder spo₂)
    } where open StrictPartialOrder

  ⊎-<-totalOrder : TotalOrder a b c →
                   TotalOrder d e f →
                   TotalOrder _ _ _
  ⊎-<-totalOrder to₁ to₂ = record
    { isTotalOrder = ⊎-<-isTotalOrder (isTotalOrder to₁) (isTotalOrder to₂)
    } where open TotalOrder

  ⊎-<-decTotalOrder : DecTotalOrder a b c →
                      DecTotalOrder d e f →
                      DecTotalOrder _ _ _
  ⊎-<-decTotalOrder to₁ to₂ = record
    { isDecTotalOrder = ⊎-<-isDecTotalOrder (isDecTotalOrder to₁) (isDecTotalOrder to₂)
    } where open DecTotalOrder

  ⊎-<-strictTotalOrder : StrictTotalOrder a b c →
                         StrictTotalOrder a b c →
                         StrictTotalOrder _ _ _
  ⊎-<-strictTotalOrder sto₁ sto₂ = record
    { isStrictTotalOrder = ⊎-<-isStrictTotalOrder (isStrictTotalOrder sto₁) (isStrictTotalOrder sto₂)
    } where open StrictTotalOrder
