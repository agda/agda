------------------------------------------------------------------------
-- Many properties which hold for _∼_ also hold for _∼_ on₁ f
------------------------------------------------------------------------

open import Relation.Binary

module Relation.Binary.On {A B : Set} (f : B → A) where

open import Data.Function
open import Data.Product

implies : ∀ ≈ ∼ → ≈ ⇒ ∼ → (≈ on₁ f) ⇒ (∼ on₁ f)
implies _ _ impl = impl

reflexive : ∀ ∼ → Reflexive ∼ → Reflexive (∼ on₁ f)
reflexive _ refl = refl

irreflexive : ∀ ≈ ∼ → Irreflexive ≈ ∼ → Irreflexive (≈ on₁ f) (∼ on₁ f)
irreflexive _ _ irrefl = irrefl

symmetric : ∀ ∼ → Symmetric ∼ → Symmetric (∼ on₁ f)
symmetric _ sym = sym

transitive : ∀ ∼ → Transitive ∼ → Transitive (∼ on₁ f)
transitive _ trans = trans

antisymmetric : ∀ ≈ ≤ →
                Antisymmetric ≈ ≤ → Antisymmetric (≈ on₁ f) (≤ on₁ f)
antisymmetric _ _ antisym = antisym

asymmetric : ∀ < → Asymmetric < → Asymmetric (< on₁ f)
asymmetric _ asym = asym

respects : ∀ ∼ P → P Respects ∼ → (P ∘₀ f) Respects (∼ on₁ f)
respects _ _ resp = resp

respects₂ : ∀ ∼₁ ∼₂ → ∼₁ Respects₂ ∼₂ → (∼₁ on₁ f) Respects₂ (∼₂ on₁ f)
respects₂ _ _ (resp₁ , resp₂) =
  ((λ {_} {_} {_} → resp₁) , λ {_} {_} {_} → resp₂)

decidable : ∀ ∼ → Decidable ∼ → Decidable (∼ on₁ f)
decidable _ dec = λ x y → dec (f x) (f y)

total : ∀ ∼ → Total ∼ → Total (∼ on₁ f)
total _ tot = λ x y → tot (f x) (f y)

trichotomous : ∀ ≈ < →
               Trichotomous ≈ < → Trichotomous (≈ on₁ f) (< on₁ f)
trichotomous _ _ compare = λ x y → compare (f x) (f y)

isEquivalence : ∀ {≈} → IsEquivalence ≈ → IsEquivalence (≈ on₁ f)
isEquivalence {≈} eq = record
  { refl  = reflexive  ≈ Eq.refl
  ; sym   = symmetric  ≈ Eq.sym
  ; trans = transitive ≈ Eq.trans
  }
  where module Eq = IsEquivalence eq

isPreorder : ∀ {≈ ∼} → IsPreorder ≈ ∼ → IsPreorder (≈ on₁ f) (∼ on₁ f)
isPreorder {≈} {∼} pre = record
  { isEquivalence = isEquivalence Pre.isEquivalence
  ; reflexive     = implies ≈ ∼ Pre.reflexive
  ; trans         = transitive ∼ Pre.trans
  ; ∼-resp-≈      = respects₂ ∼ ≈ Pre.∼-resp-≈
  }
  where module Pre = IsPreorder pre

isDecEquivalence : ∀ {≈} →
                   IsDecEquivalence ≈ → IsDecEquivalence (≈ on₁ f)
isDecEquivalence {≈} dec = record
  { isEquivalence = isEquivalence Dec.isEquivalence
  ; _≟_           = decidable ≈ Dec._≟_
  }
  where module Dec = IsDecEquivalence dec

isPartialOrder : ∀ {≈ ≤} →
                 IsPartialOrder ≈ ≤ →
                 IsPartialOrder (≈ on₁ f) (≤ on₁ f)
isPartialOrder {≈} {≤} po = record
  { isPreorder = isPreorder Po.isPreorder
  ; antisym    = antisymmetric ≈ ≤ Po.antisym
  }
  where module Po = IsPartialOrder po

isStrictPartialOrder : ∀ {≈ <} →
                       IsStrictPartialOrder ≈ < →
                       IsStrictPartialOrder (≈ on₁ f) (< on₁ f)
isStrictPartialOrder {≈} {<} spo = record
  { isEquivalence = isEquivalence Spo.isEquivalence
  ; irrefl        = irreflexive ≈ < Spo.irrefl
  ; trans         = transitive < Spo.trans
  ; <-resp-≈      = respects₂ < ≈ Spo.<-resp-≈
  }
  where module Spo = IsStrictPartialOrder spo

isTotalOrder : ∀ {≈ ≤} →
               IsTotalOrder ≈ ≤ →
               IsTotalOrder (≈ on₁ f) (≤ on₁ f)
isTotalOrder {≈} {≤} to = record
  { isPartialOrder = isPartialOrder To.isPartialOrder
  ; total          = total ≤ To.total
  }
  where module To = IsTotalOrder to

isDecTotalOrder : ∀ {≈ ≤} →
                  IsDecTotalOrder ≈ ≤ →
                  IsDecTotalOrder (≈ on₁ f) (≤ on₁ f)
isDecTotalOrder {≈} {≤} dec = record
  { isTotalOrder = isTotalOrder Dec.isTotalOrder
  ; _≟_          = decidable ≈ Dec._≟_
  ; _≤?_         = decidable ≤ Dec._≤?_
  }
  where module Dec = IsDecTotalOrder dec

isStrictTotalOrder : ∀ {≈ <} →
                     IsStrictTotalOrder ≈ < →
                       IsStrictTotalOrder (≈ on₁ f) (< on₁ f)
isStrictTotalOrder {≈} {<} sto = record
  { isEquivalence = isEquivalence Sto.isEquivalence
  ; trans         = transitive < Sto.trans
  ; compare       = trichotomous ≈ < Sto.compare
  ; <-resp-≈      = respects₂ < ≈ Sto.<-resp-≈
  }
  where module Sto = IsStrictTotalOrder sto
