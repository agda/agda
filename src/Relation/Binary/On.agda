------------------------------------------------------------------------
-- Many properties which hold for _∼_ also hold for _∼_ on f
------------------------------------------------------------------------

{-# OPTIONS --universe-polymorphism #-}

open import Relation.Binary

module Relation.Binary.On {a b} {A : Set a} {B : Set b}
                          (f : B → A) where

open import Function
open import Data.Product

implies : ∀ {ℓ₁ ℓ₂} (≈ : Rel A ℓ₁) (∼ : Rel A ℓ₂) →
          ≈ ⇒ ∼ → (≈ on f) ⇒ (∼ on f)
implies _ _ impl = impl

reflexive : ∀ {ℓ} (∼ : Rel A ℓ) → Reflexive ∼ → Reflexive (∼ on f)
reflexive _ refl = refl

irreflexive : ∀ {ℓ₁ ℓ₂} (≈ : Rel A ℓ₁) (∼ : Rel A ℓ₂) →
              Irreflexive ≈ ∼ → Irreflexive (≈ on f) (∼ on f)
irreflexive _ _ irrefl = irrefl

symmetric : ∀ {ℓ} (∼ : Rel A ℓ) → Symmetric ∼ → Symmetric (∼ on f)
symmetric _ sym = sym

transitive : ∀ {ℓ} (∼ : Rel A ℓ) → Transitive ∼ → Transitive (∼ on f)
transitive _ trans = trans

antisymmetric : ∀ {ℓ₁ ℓ₂} (≈ : Rel A ℓ₁) (≤ : Rel A ℓ₂) →
                Antisymmetric ≈ ≤ → Antisymmetric (≈ on f) (≤ on f)
antisymmetric _ _ antisym = antisym

asymmetric : ∀ {ℓ} (< : Rel A ℓ) → Asymmetric < → Asymmetric (< on f)
asymmetric _ asym = asym

respects : ∀ {ℓ p} (∼ : Rel A ℓ) (P : A → Set p) →
           P Respects ∼ → (P ∘ f) Respects (∼ on f)
respects _ _ resp = resp

respects₂ : ∀ {ℓ₁ ℓ₂} (∼₁ : Rel A ℓ₁) (∼₂ : Rel A ℓ₂) →
            ∼₁ Respects₂ ∼₂ → (∼₁ on f) Respects₂ (∼₂ on f)
respects₂ _ _ (resp₁ , resp₂) =
  ((λ {_} {_} {_} → resp₁) , λ {_} {_} {_} → resp₂)

decidable : ∀ {ℓ} (∼ : Rel A ℓ) → Decidable ∼ → Decidable (∼ on f)
decidable _ dec = λ x y → dec (f x) (f y)

total : ∀ {ℓ} (∼ : Rel A ℓ) → Total ∼ → Total (∼ on f)
total _ tot = λ x y → tot (f x) (f y)

trichotomous : ∀ {ℓ₁ ℓ₂} (≈ : Rel A ℓ₁) (< : Rel A ℓ₂) →
               Trichotomous ≈ < → Trichotomous (≈ on f) (< on f)
trichotomous _ _ compare = λ x y → compare (f x) (f y)

isEquivalence : ∀ {ℓ} {≈ : Rel A ℓ} →
                IsEquivalence ≈ → IsEquivalence (≈ on f)
isEquivalence {≈ = ≈} eq = record
  { refl  = reflexive  ≈ Eq.refl
  ; sym   = symmetric  ≈ Eq.sym
  ; trans = transitive ≈ Eq.trans
  }
  where module Eq = IsEquivalence eq

isPreorder : ∀ {ℓ₁ ℓ₂} {≈ : Rel A ℓ₁} {∼ : Rel A ℓ₂} →
             IsPreorder ≈ ∼ → IsPreorder (≈ on f) (∼ on f)
isPreorder {≈ = ≈} {∼} pre = record
  { isEquivalence = isEquivalence Pre.isEquivalence
  ; reflexive     = implies ≈ ∼ Pre.reflexive
  ; trans         = transitive ∼ Pre.trans
  }
  where module Pre = IsPreorder pre

isDecEquivalence : ∀ {ℓ} {≈ : Rel A ℓ} →
                   IsDecEquivalence ≈ → IsDecEquivalence (≈ on f)
isDecEquivalence {≈ = ≈} dec = record
  { isEquivalence = isEquivalence Dec.isEquivalence
  ; _≟_           = decidable ≈ Dec._≟_
  }
  where module Dec = IsDecEquivalence dec

isPartialOrder : ∀ {ℓ₁ ℓ₂} {≈ : Rel A ℓ₁} {≤ : Rel A ℓ₂} →
                 IsPartialOrder ≈ ≤ →
                 IsPartialOrder (≈ on f) (≤ on f)
isPartialOrder {≈ = ≈} {≤} po = record
  { isPreorder = isPreorder Po.isPreorder
  ; antisym    = antisymmetric ≈ ≤ Po.antisym
  }
  where module Po = IsPartialOrder po

isStrictPartialOrder : ∀ {ℓ₁ ℓ₂} {≈ : Rel A ℓ₁} {< : Rel A ℓ₂} →
                       IsStrictPartialOrder ≈ < →
                       IsStrictPartialOrder (≈ on f) (< on f)
isStrictPartialOrder {≈ = ≈} {<} spo = record
  { isEquivalence = isEquivalence Spo.isEquivalence
  ; irrefl        = irreflexive ≈ < Spo.irrefl
  ; trans         = transitive < Spo.trans
  ; <-resp-≈      = respects₂ < ≈ Spo.<-resp-≈
  }
  where module Spo = IsStrictPartialOrder spo

isTotalOrder : ∀ {ℓ₁ ℓ₂} {≈ : Rel A ℓ₁} {≤ : Rel A ℓ₂} →
               IsTotalOrder ≈ ≤ →
               IsTotalOrder (≈ on f) (≤ on f)
isTotalOrder {≈ = ≈} {≤} to = record
  { isPartialOrder = isPartialOrder To.isPartialOrder
  ; total          = total ≤ To.total
  }
  where module To = IsTotalOrder to

isDecTotalOrder : ∀ {ℓ₁ ℓ₂} {≈ : Rel A ℓ₁} {≤ : Rel A ℓ₂} →
                  IsDecTotalOrder ≈ ≤ →
                  IsDecTotalOrder (≈ on f) (≤ on f)
isDecTotalOrder {≈ = ≈} {≤} dec = record
  { isTotalOrder = isTotalOrder Dec.isTotalOrder
  ; _≟_          = decidable ≈ Dec._≟_
  ; _≤?_         = decidable ≤ Dec._≤?_
  }
  where module Dec = IsDecTotalOrder dec

isStrictTotalOrder : ∀ {ℓ₁ ℓ₂} {≈ : Rel A ℓ₁} {< : Rel A ℓ₂} →
                     IsStrictTotalOrder ≈ < →
                       IsStrictTotalOrder (≈ on f) (< on f)
isStrictTotalOrder {≈ = ≈} {<} sto = record
  { isEquivalence = isEquivalence Sto.isEquivalence
  ; trans         = transitive < Sto.trans
  ; compare       = trichotomous ≈ < Sto.compare
  ; <-resp-≈      = respects₂ < ≈ Sto.<-resp-≈
  }
  where module Sto = IsStrictTotalOrder sto
