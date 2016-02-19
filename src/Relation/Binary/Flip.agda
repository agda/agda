------------------------------------------------------------------------
-- The Agda standard library
--
-- Many properties which hold for _∼_ also hold for flip _∼_
------------------------------------------------------------------------

open import Relation.Binary

module Relation.Binary.Flip where

open import Function
open import Data.Product

implies : ∀ {a b ℓ₁ ℓ₂} {A : Set a} {B : Set b}
          (≈ : REL A B ℓ₁) (∼ : REL A B ℓ₂) →
          ≈ ⇒ ∼ → flip ≈ ⇒ flip ∼
implies _ _ impl = impl

reflexive : ∀ {a ℓ} {A : Set a} (∼ : Rel A ℓ) →
            Reflexive ∼ → Reflexive (flip ∼)
reflexive _ refl = refl

irreflexive : ∀ {a b ℓ₁ ℓ₂} {A : Set a} {B : Set b}
              (≈ : REL A B ℓ₁) (∼ : REL A B ℓ₂) →
              Irreflexive ≈ ∼ → Irreflexive (flip ≈) (flip ∼)
irreflexive _ _ irrefl = irrefl

symmetric : ∀ {a ℓ} {A : Set a} (∼ : Rel A ℓ) →
            Symmetric ∼ → Symmetric (flip ∼)
symmetric _ sym = sym

transitive : ∀ {a ℓ} {A : Set a} (∼ : Rel A ℓ) →
             Transitive ∼ → Transitive (flip ∼)
transitive _ trans = flip trans

antisymmetric : ∀ {a ℓ₁ ℓ₂} {A : Set a} (≈ : Rel A ℓ₁) (≤ : Rel A ℓ₂) →
                Antisymmetric ≈ ≤ → Antisymmetric (flip ≈) (flip ≤)
antisymmetric _ _ antisym = antisym

asymmetric : ∀ {a ℓ} {A : Set a} (< : Rel A ℓ) →
             Asymmetric < → Asymmetric (flip <)
asymmetric _ asym = asym

respects : ∀ {a ℓ p} {A : Set a} (∼ : Rel A ℓ) (P : A → Set p) →
           Symmetric ∼ → P Respects ∼ → P Respects flip ∼
respects _ _ sym resp ∼ = resp (sym ∼)

respects₂ : ∀ {a ℓ₁ ℓ₂} {A : Set a} (∼₁ : Rel A ℓ₁) (∼₂ : Rel A ℓ₂) →
            Symmetric ∼₂ → ∼₁ Respects₂ ∼₂ → flip ∼₁ Respects₂ flip ∼₂
respects₂ _ _ sym (resp₁ , resp₂) =
  ((λ {_} {_} {_} ∼ → resp₂ (sym ∼)) , λ {_} {_} {_} ∼ → resp₁ (sym ∼))

decidable : ∀ {a b ℓ} {A : Set a} {B : Set b} (∼ : REL A B ℓ) →
            Decidable ∼ → Decidable (flip ∼)
decidable _ dec x y = dec y x

total : ∀ {a ℓ} {A : Set a} (∼ : Rel A ℓ) →
        Total ∼ → Total (flip ∼)
total _ tot x y = tot y x

trichotomous : ∀ {a ℓ₁ ℓ₂} {A : Set a} (≈ : Rel A ℓ₁) (< : Rel A ℓ₂) →
               Trichotomous ≈ < → Trichotomous (flip ≈) (flip <)
trichotomous _ _ compare x y = compare y x

isEquivalence : ∀ {a ℓ} {A : Set a} {≈ : Rel A ℓ} →
                IsEquivalence ≈ → IsEquivalence (flip ≈)
isEquivalence {≈ = ≈} eq = record
  { refl  = reflexive  ≈ Eq.refl
  ; sym   = symmetric  ≈ Eq.sym
  ; trans = transitive ≈ Eq.trans
  }
  where module Eq = IsEquivalence eq

setoid : ∀ {s₁ s₂} → Setoid s₁ s₂ → Setoid s₁ s₂
setoid S = record
  { _≈_           = flip S._≈_
  ; isEquivalence = isEquivalence S.isEquivalence
  } where module S = Setoid S

isPreorder : ∀ {a ℓ₁ ℓ₂} {A : Set a} {≈ : Rel A ℓ₁} {∼ : Rel A ℓ₂} →
             IsPreorder ≈ ∼ → IsPreorder (flip ≈) (flip ∼)
isPreorder {≈ = ≈} {∼} pre = record
  { isEquivalence = isEquivalence Pre.isEquivalence
  ; reflexive     = implies ≈ ∼ Pre.reflexive
  ; trans         = transitive ∼ Pre.trans
  }
  where module Pre = IsPreorder pre

preorder : ∀ {p₁ p₂ p₃} → Preorder p₁ p₂ p₃ → Preorder p₁ p₂ p₃
preorder P = record
  { _∼_        = flip P._∼_
  ; _≈_        = flip P._≈_
  ; isPreorder = isPreorder P.isPreorder
  } where module P = Preorder P

isDecEquivalence : ∀ {a ℓ} {A : Set a} {≈ : Rel A ℓ} →
                   IsDecEquivalence ≈ → IsDecEquivalence (flip ≈)
isDecEquivalence {≈ = ≈} dec = record
  { isEquivalence = isEquivalence Dec.isEquivalence
  ; _≟_           = decidable ≈ Dec._≟_
  }
  where module Dec = IsDecEquivalence dec

decSetoid : ∀ {s₁ s₂} → DecSetoid s₁ s₂ → DecSetoid s₁ s₂
decSetoid S = record
  { _≈_              = flip S._≈_
  ; isDecEquivalence = isDecEquivalence S.isDecEquivalence
  } where module S = DecSetoid S

isPartialOrder : ∀ {a ℓ₁ ℓ₂} {A : Set a} {≈ : Rel A ℓ₁} {≤ : Rel A ℓ₂} →
                 IsPartialOrder ≈ ≤ →
                 IsPartialOrder (flip ≈) (flip ≤)
isPartialOrder {≈ = ≈} {≤} po = record
  { isPreorder = isPreorder Po.isPreorder
  ; antisym    = antisymmetric ≈ ≤ Po.antisym
  }
  where module Po = IsPartialOrder po

poset : ∀ {p₁ p₂ p₃} → Poset p₁ p₂ p₃ → Poset p₁ p₂ p₃
poset O = record
  { _≈_            = flip O._≈_
  ; _≤_            = flip O._≤_
  ; isPartialOrder = isPartialOrder O.isPartialOrder
  } where module O = Poset O

isStrictPartialOrder :
  ∀ {a ℓ₁ ℓ₂} {A : Set a} {≈ : Rel A ℓ₁} {< : Rel A ℓ₂} →
  IsStrictPartialOrder ≈ < → IsStrictPartialOrder (flip ≈) (flip <)
isStrictPartialOrder {≈ = ≈} {<} spo = record
  { isEquivalence = isEquivalence Spo.isEquivalence
  ; irrefl        = irreflexive ≈ < Spo.irrefl
  ; trans         = transitive < Spo.trans
  ; <-resp-≈      = respects₂ < ≈ Spo.Eq.sym Spo.<-resp-≈
  }
  where module Spo = IsStrictPartialOrder spo

strictPartialOrder :
  ∀ {s₁ s₂ s₃} →
  StrictPartialOrder s₁ s₂ s₃ → StrictPartialOrder s₁ s₂ s₃
strictPartialOrder O = record
  { _≈_                  = flip O._≈_
  ; _<_                  = flip O._<_
  ; isStrictPartialOrder = isStrictPartialOrder O.isStrictPartialOrder
  } where module O = StrictPartialOrder O

isTotalOrder :
  ∀ {a ℓ₁ ℓ₂} {A : Set a} {≈ : Rel A ℓ₁} {≤ : Rel A ℓ₂} →
  IsTotalOrder ≈ ≤ → IsTotalOrder (flip ≈) (flip ≤)
isTotalOrder {≈ = ≈} {≤} to = record
  { isPartialOrder = isPartialOrder To.isPartialOrder
  ; total          = total ≤ To.total
  }
  where module To = IsTotalOrder to

totalOrder : ∀ {t₁ t₂ t₃} → TotalOrder t₁ t₂ t₃ → TotalOrder t₁ t₂ t₃
totalOrder O = record
  { _≈_          = flip O._≈_
  ; _≤_          = flip O._≤_
  ; isTotalOrder = isTotalOrder O.isTotalOrder
  } where module O = TotalOrder O

isDecTotalOrder :
  ∀ {a ℓ₁ ℓ₂} {A : Set a} {≈ : Rel A ℓ₁} {≤ : Rel A ℓ₂} →
  IsDecTotalOrder ≈ ≤ → IsDecTotalOrder (flip ≈) (flip ≤)
isDecTotalOrder {≈ = ≈} {≤} dec = record
  { isTotalOrder = isTotalOrder Dec.isTotalOrder
  ; _≟_          = decidable ≈ Dec._≟_
  ; _≤?_         = decidable ≤ Dec._≤?_
  }
  where module Dec = IsDecTotalOrder dec

decTotalOrder :
  ∀ {d₁ d₂ d₃} → DecTotalOrder d₁ d₂ d₃ → DecTotalOrder d₁ d₂ d₃
decTotalOrder O = record
  { _≈_             = flip O._≈_
  ; _≤_             = flip O._≤_
  ; isDecTotalOrder = isDecTotalOrder O.isDecTotalOrder
  } where module O = DecTotalOrder O

isStrictTotalOrder :
  ∀ {a ℓ₁ ℓ₂} {A : Set a} {≈ : Rel A ℓ₁} {< : Rel A ℓ₂} →
  IsStrictTotalOrder ≈ < → IsStrictTotalOrder (flip ≈) (flip <)
isStrictTotalOrder {≈ = ≈} {<} sto = record
  { isEquivalence = isEquivalence Sto.isEquivalence
  ; trans         = transitive < Sto.trans
  ; compare       = trichotomous ≈ < Sto.compare
  }
  where module Sto = IsStrictTotalOrder sto

strictTotalOrder :
  ∀ {s₁ s₂ s₃} → StrictTotalOrder s₁ s₂ s₃ → StrictTotalOrder s₁ s₂ s₃
strictTotalOrder O = record
  { _≈_                = flip O._≈_
  ; _<_                = flip O._<_
  ; isStrictTotalOrder = isStrictTotalOrder O.isStrictTotalOrder
  } where module O = StrictTotalOrder O
