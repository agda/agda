------------------------------------------------------------------------
-- The Agda standard library
--
-- Many properties which hold for _∼_ also hold for _∼_ on f
------------------------------------------------------------------------

open import Relation.Binary

module Relation.Binary.On where

open import Function
open import Data.Product

module _ {a b} {A : Set a} {B : Set b} (f : B → A) where

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

  isDecPartialOrder : ∀ {ℓ₁ ℓ₂} {≈ : Rel A ℓ₁} {≤ : Rel A ℓ₂} →
                      IsDecPartialOrder ≈ ≤ →
                      IsDecPartialOrder (≈ on f) (≤ on f)
  isDecPartialOrder dpo = record
    { isPartialOrder = isPartialOrder DPO.isPartialOrder
    ; _≟_            = decidable _ DPO._≟_
    ; _≤?_           = decidable _ DPO._≤?_
    }
    where module DPO = IsDecPartialOrder dpo

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
    }
    where module Sto = IsStrictTotalOrder sto

preorder : ∀ {p₁ p₂ p₃ b} {B : Set b} (P : Preorder p₁ p₂ p₃) →
           (B → Preorder.Carrier P) → Preorder _ _ _
preorder P f = record
  { isPreorder = isPreorder f (Preorder.isPreorder P)
  }

setoid : ∀ {s₁ s₂ b} {B : Set b} (S : Setoid s₁ s₂) →
         (B → Setoid.Carrier S) → Setoid _ _
setoid S f = record
  { isEquivalence = isEquivalence f (Setoid.isEquivalence S)
  }

decSetoid : ∀ {d₁ d₂ b} {B : Set b} (D : DecSetoid d₁ d₂) →
            (B → DecSetoid.Carrier D) → DecSetoid _ _
decSetoid D f = record
  { isDecEquivalence = isDecEquivalence f (DecSetoid.isDecEquivalence D)
  }

poset : ∀ {p₁ p₂ p₃ b} {B : Set b} (P : Poset p₁ p₂ p₃) →
        (B → Poset.Carrier P) → Poset _ _ _
poset P f = record
  { isPartialOrder = isPartialOrder f (Poset.isPartialOrder P)
  }

decPoset : ∀ {d₁ d₂ d₃ b} {B : Set b} (D : DecPoset d₁ d₂ d₃) →
           (B → DecPoset.Carrier D) → DecPoset _ _ _
decPoset D f = record
  { isDecPartialOrder =
      isDecPartialOrder f (DecPoset.isDecPartialOrder D)
  }

strictPartialOrder :
  ∀ {s₁ s₂ s₃ b} {B : Set b} (S : StrictPartialOrder s₁ s₂ s₃) →
  (B → StrictPartialOrder.Carrier S) → StrictPartialOrder _ _ _
strictPartialOrder S f = record
  { isStrictPartialOrder =
      isStrictPartialOrder f (StrictPartialOrder.isStrictPartialOrder S)
  }

totalOrder : ∀ {t₁ t₂ t₃ b} {B : Set b} (T : TotalOrder t₁ t₂ t₃) →
             (B → TotalOrder.Carrier T) → TotalOrder _ _ _
totalOrder T f = record
  { isTotalOrder = isTotalOrder f (TotalOrder.isTotalOrder T)
  }

decTotalOrder :
  ∀ {d₁ d₂ d₃ b} {B : Set b} (D : DecTotalOrder d₁ d₂ d₃) →
  (B → DecTotalOrder.Carrier D) → DecTotalOrder _ _ _
decTotalOrder D f = record
  { isDecTotalOrder = isDecTotalOrder f (DecTotalOrder.isDecTotalOrder D)
  }

strictTotalOrder :
  ∀ {s₁ s₂ s₃ b} {B : Set b} (S : StrictTotalOrder s₁ s₂ s₃) →
  (B → StrictTotalOrder.Carrier S) → StrictTotalOrder _ _ _
strictTotalOrder S f = record
  { isStrictTotalOrder =
      isStrictTotalOrder f (StrictTotalOrder.isStrictTotalOrder S)
  }
