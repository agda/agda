------------------------------------------------------------------------
-- Many properties which hold for _∼_ also hold for flip _∼_
------------------------------------------------------------------------

open import Relation.Binary

module Relation.Binary.Flip where

open import Data.Function
open import Data.Product

implies : ∀ {A} (≈ ∼ : Rel A) → ≈ ⇒ ∼ → flip ≈ ⇒ flip ∼
implies _ _ impl = impl

reflexive : ∀ {A} (∼ : Rel A) → Reflexive ∼ → Reflexive (flip ∼)
reflexive _ refl = refl

irreflexive : ∀ {A} (≈ ∼ : Rel A) →
              Irreflexive ≈ ∼ → Irreflexive (flip ≈) (flip ∼)
irreflexive _ _ irrefl = irrefl

symmetric : ∀ {A} (∼ : Rel A) → Symmetric ∼ → Symmetric (flip ∼)
symmetric _ sym = sym

transitive : ∀ {A} (∼ : Rel A) → Transitive ∼ → Transitive (flip ∼)
transitive _ trans = flip trans

antisymmetric : ∀ {A} (≈ ≤ : Rel A) →
                Antisymmetric ≈ ≤ → Antisymmetric (flip ≈) (flip ≤)
antisymmetric _ _ antisym = antisym

asymmetric : ∀ {A} (< : Rel A) → Asymmetric < → Asymmetric (flip <)
asymmetric _ asym = asym

respects : ∀ {A} (∼ : Rel A) P →
           Symmetric ∼ → P Respects ∼ → P Respects flip ∼
respects _ _ sym resp ∼ = resp (sym ∼)

respects₂ : ∀ {A} (∼₁ ∼₂ : Rel A) →
            Symmetric ∼₂ → ∼₁ Respects₂ ∼₂ → flip ∼₁ Respects₂ flip ∼₂
respects₂ _ _ sym (resp₁ , resp₂) =
  ((λ {_} {_} {_} ∼ → resp₂ (sym ∼)) , λ {_} {_} {_} ∼ → resp₁ (sym ∼))

decidable : ∀ {A} (∼ : Rel A) → Decidable ∼ → Decidable (flip ∼)
decidable _ dec x y = dec y x

total : ∀ {A} (∼ : Rel A) → Total ∼ → Total (flip ∼)
total _ tot x y = tot y x

trichotomous : ∀ {A} (≈ < : Rel A) →
               Trichotomous ≈ < → Trichotomous (flip ≈) (flip <)
trichotomous _ _ compare x y = compare y x

isEquivalence : ∀ {A} {≈ : Rel A} →
                IsEquivalence ≈ → IsEquivalence (flip ≈)
isEquivalence {≈ = ≈} eq = record
  { refl  = reflexive  ≈ Eq.refl
  ; sym   = symmetric  ≈ Eq.sym
  ; trans = transitive ≈ Eq.trans
  }
  where module Eq = IsEquivalence eq

setoid : Setoid → Setoid
setoid S = record
  { _≈_           = flip S._≈_
  ; isEquivalence = isEquivalence S.isEquivalence
  } where module S = Setoid S

isPreorder : ∀ {A} {≈ ∼ : Rel A} →
             IsPreorder ≈ ∼ → IsPreorder (flip ≈) (flip ∼)
isPreorder {≈ = ≈} {∼} pre = record
  { isEquivalence = isEquivalence Pre.isEquivalence
  ; reflexive     = implies ≈ ∼ Pre.reflexive
  ; trans         = transitive ∼ Pre.trans
  ; ∼-resp-≈      = respects₂ ∼ ≈ Pre.Eq.sym Pre.∼-resp-≈
  }
  where module Pre = IsPreorder pre

preorder : Preorder → Preorder
preorder P = record
  { _∼_        = flip P._∼_
  ; _≈_        = flip P._≈_
  ; isPreorder = isPreorder P.isPreorder
  } where module P = Preorder P

isDecEquivalence : ∀ {A} {≈ : Rel A} →
                   IsDecEquivalence ≈ → IsDecEquivalence (flip ≈)
isDecEquivalence {≈ = ≈} dec = record
  { isEquivalence = isEquivalence Dec.isEquivalence
  ; _≟_           = decidable ≈ Dec._≟_
  }
  where module Dec = IsDecEquivalence dec

decSetoid : DecSetoid → DecSetoid
decSetoid S = record
  { _≈_              = flip S._≈_
  ; isDecEquivalence = isDecEquivalence S.isDecEquivalence
  } where module S = DecSetoid S

isPartialOrder : ∀ {A} {≈ ≤ : Rel A} →
                 IsPartialOrder ≈ ≤ →
                 IsPartialOrder (flip ≈) (flip ≤)
isPartialOrder {≈ = ≈} {≤} po = record
  { isPreorder = isPreorder Po.isPreorder
  ; antisym    = antisymmetric ≈ ≤ Po.antisym
  }
  where module Po = IsPartialOrder po

poset : Poset → Poset
poset O = record
  { _≈_            = flip O._≈_
  ; _≤_            = flip O._≤_
  ; isPartialOrder = isPartialOrder O.isPartialOrder
  } where module O = Poset O

isStrictPartialOrder : ∀ {A} {≈ < : Rel A} →
                       IsStrictPartialOrder ≈ < →
                       IsStrictPartialOrder (flip ≈) (flip <)
isStrictPartialOrder {≈ = ≈} {<} spo = record
  { isEquivalence = isEquivalence Spo.isEquivalence
  ; irrefl        = irreflexive ≈ < Spo.irrefl
  ; trans         = transitive < Spo.trans
  ; <-resp-≈      = respects₂ < ≈ Spo.Eq.sym Spo.<-resp-≈
  }
  where module Spo = IsStrictPartialOrder spo

strictPartialOrder : StrictPartialOrder → StrictPartialOrder
strictPartialOrder O = record
  { _≈_                  = flip O._≈_
  ; _<_                  = flip O._<_
  ; isStrictPartialOrder = isStrictPartialOrder O.isStrictPartialOrder
  } where module O = StrictPartialOrder O

isTotalOrder : ∀ {A} {≈ ≤ : Rel A} →
               IsTotalOrder ≈ ≤ →
               IsTotalOrder (flip ≈) (flip ≤)
isTotalOrder {≈ = ≈} {≤} to = record
  { isPartialOrder = isPartialOrder To.isPartialOrder
  ; total          = total ≤ To.total
  }
  where module To = IsTotalOrder to

totalOrder : TotalOrder → TotalOrder
totalOrder O = record
  { _≈_          = flip O._≈_
  ; _≤_          = flip O._≤_
  ; isTotalOrder = isTotalOrder O.isTotalOrder
  } where module O = TotalOrder O

isDecTotalOrder : ∀ {A} {≈ ≤ : Rel A} →
                  IsDecTotalOrder ≈ ≤ →
                  IsDecTotalOrder (flip ≈) (flip ≤)
isDecTotalOrder {≈ = ≈} {≤} dec = record
  { isTotalOrder = isTotalOrder Dec.isTotalOrder
  ; _≟_          = decidable ≈ Dec._≟_
  ; _≤?_         = decidable ≤ Dec._≤?_
  }
  where module Dec = IsDecTotalOrder dec

decTotalOrder : DecTotalOrder → DecTotalOrder
decTotalOrder O = record
  { _≈_             = flip O._≈_
  ; _≤_             = flip O._≤_
  ; isDecTotalOrder = isDecTotalOrder O.isDecTotalOrder
  } where module O = DecTotalOrder O

isStrictTotalOrder : ∀ {A} {≈ < : Rel A} →
                     IsStrictTotalOrder ≈ < →
                       IsStrictTotalOrder (flip ≈) (flip <)
isStrictTotalOrder {≈ = ≈} {<} sto = record
  { isEquivalence = isEquivalence Sto.isEquivalence
  ; trans         = transitive < Sto.trans
  ; compare       = trichotomous ≈ < Sto.compare
  ; <-resp-≈      = respects₂ < ≈ Sto.Eq.sym Sto.<-resp-≈
  }
  where module Sto = IsStrictTotalOrder sto

strictTotalOrder : StrictTotalOrder → StrictTotalOrder
strictTotalOrder O = record
  { _≈_                = flip O._≈_
  ; _<_                = flip O._<_
  ; isStrictTotalOrder = isStrictTotalOrder O.isStrictTotalOrder
  } where module O = StrictTotalOrder O
