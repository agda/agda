------------------------------------------------------------------------
-- Many properties which hold for _∼_ also hold for _∼_ on f
------------------------------------------------------------------------

open import Relation.Binary

module Relation.Binary.On {A B : Set} (f : B → A) where

open import Data.Function
open import Data.Product

implies : ∀ ≈ ∼ → ≈ ⇒ ∼ → (≈ on f) ⇒ (∼ on f)
implies _ _ impl = impl

reflexive : ∀ ∼ → Reflexive ∼ → Reflexive (∼ on f)
reflexive _ refl = refl

irreflexive : ∀ ≈ ∼ → Irreflexive ≈ ∼ → Irreflexive (≈ on f) (∼ on f)
irreflexive _ _ irrefl = irrefl

symmetric : ∀ ∼ → Symmetric ∼ → Symmetric (∼ on f)
symmetric _ sym = sym

transitive : ∀ ∼ → Transitive ∼ → Transitive (∼ on f)
transitive _ trans = trans

antisymmetric : ∀ ≈ ≤ →
                Antisymmetric ≈ ≤ → Antisymmetric (≈ on f) (≤ on f)
antisymmetric _ _ antisym = antisym

asymmetric : ∀ < → Asymmetric < → Asymmetric (< on f)
asymmetric _ asym = asym

respects : ∀ ∼ P → P Respects ∼ → (P ∘ f) Respects (∼ on f)
respects _ _ resp = resp

respects₂ : ∀ ∼₁ ∼₂ → ∼₁ Respects₂ ∼₂ → (∼₁ on f) Respects₂ (∼₂ on f)
respects₂ _ _ (resp₁ , resp₂) =
  ((λ {_} {_} {_} → resp₁) , λ {_} {_} {_} → resp₂)

decidable : ∀ ∼ → Decidable ∼ → Decidable (∼ on f)
decidable _ dec = λ x y → dec (f x) (f y)

total : ∀ ∼ → Total ∼ → Total (∼ on f)
total _ tot = λ x y → tot (f x) (f y)

trichotomous : ∀ ≈ < →
               Trichotomous ≈ < → Trichotomous (≈ on f) (< on f)
trichotomous _ _ compare = λ x y → compare (f x) (f y)

isEquivalence : ∀ {≈} → IsEquivalence ≈ → IsEquivalence (≈ on f)
isEquivalence {≈} eq = record
  { refl  = reflexive  ≈ Eq.refl
  ; sym   = symmetric  ≈ Eq.sym
  ; trans = transitive ≈ Eq.trans
  }
  where module Eq = IsEquivalence eq

isPreorder : ∀ {≈ ∼} → IsPreorder ≈ ∼ → IsPreorder (≈ on f) (∼ on f)
isPreorder {≈} {∼} pre = record
  { isEquivalence = isEquivalence Pre.isEquivalence
  ; reflexive     = implies ≈ ∼ Pre.reflexive
  ; trans         = transitive ∼ Pre.trans
  ; ∼-resp-≈      = respects₂ ∼ ≈ Pre.∼-resp-≈
  }
  where module Pre = IsPreorder pre

isDecEquivalence : ∀ {≈} →
                   IsDecEquivalence ≈ → IsDecEquivalence (≈ on f)
isDecEquivalence {≈} dec = record
  { isEquivalence = isEquivalence Dec.isEquivalence
  ; _≟_           = decidable ≈ Dec._≟_
  }
  where module Dec = IsDecEquivalence dec

isPartialOrder : ∀ {≈ ≤} →
                 IsPartialOrder ≈ ≤ →
                 IsPartialOrder (≈ on f) (≤ on f)
isPartialOrder {≈} {≤} po = record
  { isPreorder = isPreorder Po.isPreorder
  ; antisym    = antisymmetric ≈ ≤ Po.antisym
  }
  where module Po = IsPartialOrder po

isStrictPartialOrder : ∀ {≈ <} →
                       IsStrictPartialOrder ≈ < →
                       IsStrictPartialOrder (≈ on f) (< on f)
isStrictPartialOrder {≈} {<} spo = record
  { isEquivalence = isEquivalence Spo.isEquivalence
  ; irrefl        = irreflexive ≈ < Spo.irrefl
  ; trans         = transitive < Spo.trans
  ; <-resp-≈      = respects₂ < ≈ Spo.<-resp-≈
  }
  where module Spo = IsStrictPartialOrder spo

isTotalOrder : ∀ {≈ ≤} →
               IsTotalOrder ≈ ≤ →
               IsTotalOrder (≈ on f) (≤ on f)
isTotalOrder {≈} {≤} to = record
  { isPartialOrder = isPartialOrder To.isPartialOrder
  ; total          = total ≤ To.total
  }
  where module To = IsTotalOrder to

isDecTotalOrder : ∀ {≈ ≤} →
                  IsDecTotalOrder ≈ ≤ →
                  IsDecTotalOrder (≈ on f) (≤ on f)
isDecTotalOrder {≈} {≤} dec = record
  { isTotalOrder = isTotalOrder Dec.isTotalOrder
  ; _≟_          = decidable ≈ Dec._≟_
  ; _≤?_         = decidable ≤ Dec._≤?_
  }
  where module Dec = IsDecTotalOrder dec

isStrictTotalOrder : ∀ {≈ <} →
                     IsStrictTotalOrder ≈ < →
                       IsStrictTotalOrder (≈ on f) (< on f)
isStrictTotalOrder {≈} {<} sto = record
  { isEquivalence = isEquivalence Sto.isEquivalence
  ; trans         = transitive < Sto.trans
  ; compare       = trichotomous ≈ < Sto.compare
  ; <-resp-≈      = respects₂ < ≈ Sto.<-resp-≈
  }
  where module Sto = IsStrictTotalOrder sto
