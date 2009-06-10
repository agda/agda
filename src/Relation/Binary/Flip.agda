------------------------------------------------------------------------
-- Many properties which hold for _∼_ also hold for flip₁ _∼_
------------------------------------------------------------------------

open import Relation.Binary

module Relation.Binary.Flip where

open import Data.Function
open import Data.Product

implies : ∀ {A} (≈ ∼ : Rel A) → ≈ ⇒ ∼ → flip₁ ≈ ⇒ flip₁ ∼
implies _ _ impl = impl

reflexive : ∀ {A} (∼ : Rel A) → Reflexive ∼ → Reflexive (flip₁ ∼)
reflexive _ refl = refl

irreflexive : ∀ {A} (≈ ∼ : Rel A) →
              Irreflexive ≈ ∼ → Irreflexive (flip₁ ≈) (flip₁ ∼)
irreflexive _ _ irrefl = irrefl

symmetric : ∀ {A} (∼ : Rel A) → Symmetric ∼ → Symmetric (flip₁ ∼)
symmetric _ sym = sym

transitive : ∀ {A} (∼ : Rel A) → Transitive ∼ → Transitive (flip₁ ∼)
transitive _ trans = flip trans

antisymmetric : ∀ {A} (≈ ≤ : Rel A) →
                Antisymmetric ≈ ≤ → Antisymmetric (flip₁ ≈) (flip₁ ≤)
antisymmetric _ _ antisym = antisym

asymmetric : ∀ {A} (< : Rel A) → Asymmetric < → Asymmetric (flip₁ <)
asymmetric _ asym = asym

respects : ∀ {A} (∼ : Rel A) P →
           Symmetric ∼ → P Respects ∼ → P Respects flip₁ ∼
respects _ _ sym resp ∼ = resp (sym ∼)

respects₂ : ∀ {A} (∼₁ ∼₂ : Rel A) →
            Symmetric ∼₂ → ∼₁ Respects₂ ∼₂ → flip₁ ∼₁ Respects₂ flip₁ ∼₂
respects₂ _ _ sym (resp₁ , resp₂) =
  ((λ {_} {_} {_} ∼ → resp₂ (sym ∼)) , λ {_} {_} {_} ∼ → resp₁ (sym ∼))

decidable : ∀ {A} (∼ : Rel A) → Decidable ∼ → Decidable (flip₁ ∼)
decidable _ dec x y = dec y x

total : ∀ {A} (∼ : Rel A) → Total ∼ → Total (flip₁ ∼)
total _ tot x y = tot y x

trichotomous : ∀ {A} (≈ < : Rel A) →
               Trichotomous ≈ < → Trichotomous (flip₁ ≈) (flip₁ <)
trichotomous _ _ compare x y = compare y x

isEquivalence : ∀ {A} {≈ : Rel A} →
                IsEquivalence ≈ → IsEquivalence (flip₁ ≈)
isEquivalence {≈ = ≈} eq = record
  { refl  = reflexive  ≈ Eq.refl
  ; sym   = symmetric  ≈ Eq.sym
  ; trans = transitive ≈ Eq.trans
  }
  where module Eq = IsEquivalence eq

setoid : Setoid → Setoid
setoid S = record
  { _≈_           = flip₁ S._≈_
  ; isEquivalence = isEquivalence S.isEquivalence
  } where module S = Setoid S

isPreorder : ∀ {A} {≈ ∼ : Rel A} →
             IsPreorder ≈ ∼ → IsPreorder (flip₁ ≈) (flip₁ ∼)
isPreorder {≈ = ≈} {∼} pre = record
  { isEquivalence = isEquivalence Pre.isEquivalence
  ; reflexive     = implies ≈ ∼ Pre.reflexive
  ; trans         = transitive ∼ Pre.trans
  ; ∼-resp-≈      = respects₂ ∼ ≈ Pre.Eq.sym Pre.∼-resp-≈
  }
  where module Pre = IsPreorder pre

preorder : Preorder → Preorder
preorder P = record
  { _∼_        = flip₁ P._∼_
  ; _≈_        = flip₁ P._≈_
  ; isPreorder = isPreorder P.isPreorder
  } where module P = Preorder P

isDecEquivalence : ∀ {A} {≈ : Rel A} →
                   IsDecEquivalence ≈ → IsDecEquivalence (flip₁ ≈)
isDecEquivalence {≈ = ≈} dec = record
  { isEquivalence = isEquivalence Dec.isEquivalence
  ; _≟_           = decidable ≈ Dec._≟_
  }
  where module Dec = IsDecEquivalence dec

decSetoid : DecSetoid → DecSetoid
decSetoid S = record
  { _≈_              = flip₁ S._≈_
  ; isDecEquivalence = isDecEquivalence S.isDecEquivalence
  } where module S = DecSetoid S

isPartialOrder : ∀ {A} {≈ ≤ : Rel A} →
                 IsPartialOrder ≈ ≤ →
                 IsPartialOrder (flip₁ ≈) (flip₁ ≤)
isPartialOrder {≈ = ≈} {≤} po = record
  { isPreorder = isPreorder Po.isPreorder
  ; antisym    = antisymmetric ≈ ≤ Po.antisym
  }
  where module Po = IsPartialOrder po

poset : Poset → Poset
poset O = record
  { _≈_            = flip₁ O._≈_
  ; _≤_            = flip₁ O._≤_
  ; isPartialOrder = isPartialOrder O.isPartialOrder
  } where module O = Poset O

isStrictPartialOrder : ∀ {A} {≈ < : Rel A} →
                       IsStrictPartialOrder ≈ < →
                       IsStrictPartialOrder (flip₁ ≈) (flip₁ <)
isStrictPartialOrder {≈ = ≈} {<} spo = record
  { isEquivalence = isEquivalence Spo.isEquivalence
  ; irrefl        = irreflexive ≈ < Spo.irrefl
  ; trans         = transitive < Spo.trans
  ; <-resp-≈      = respects₂ < ≈ Spo.Eq.sym Spo.<-resp-≈
  }
  where module Spo = IsStrictPartialOrder spo

strictPartialOrder : StrictPartialOrder → StrictPartialOrder
strictPartialOrder O = record
  { _≈_                  = flip₁ O._≈_
  ; _<_                  = flip₁ O._<_
  ; isStrictPartialOrder = isStrictPartialOrder O.isStrictPartialOrder
  } where module O = StrictPartialOrder O

isTotalOrder : ∀ {A} {≈ ≤ : Rel A} →
               IsTotalOrder ≈ ≤ →
               IsTotalOrder (flip₁ ≈) (flip₁ ≤)
isTotalOrder {≈ = ≈} {≤} to = record
  { isPartialOrder = isPartialOrder To.isPartialOrder
  ; total          = total ≤ To.total
  }
  where module To = IsTotalOrder to

totalOrder : TotalOrder → TotalOrder
totalOrder O = record
  { _≈_          = flip₁ O._≈_
  ; _≤_          = flip₁ O._≤_
  ; isTotalOrder = isTotalOrder O.isTotalOrder
  } where module O = TotalOrder O

isDecTotalOrder : ∀ {A} {≈ ≤ : Rel A} →
                  IsDecTotalOrder ≈ ≤ →
                  IsDecTotalOrder (flip₁ ≈) (flip₁ ≤)
isDecTotalOrder {≈ = ≈} {≤} dec = record
  { isTotalOrder = isTotalOrder Dec.isTotalOrder
  ; _≟_          = decidable ≈ Dec._≟_
  ; _≤?_         = decidable ≤ Dec._≤?_
  }
  where module Dec = IsDecTotalOrder dec

decTotalOrder : DecTotalOrder → DecTotalOrder
decTotalOrder O = record
  { _≈_             = flip₁ O._≈_
  ; _≤_             = flip₁ O._≤_
  ; isDecTotalOrder = isDecTotalOrder O.isDecTotalOrder
  } where module O = DecTotalOrder O

isStrictTotalOrder : ∀ {A} {≈ < : Rel A} →
                     IsStrictTotalOrder ≈ < →
                       IsStrictTotalOrder (flip₁ ≈) (flip₁ <)
isStrictTotalOrder {≈ = ≈} {<} sto = record
  { isEquivalence = isEquivalence Sto.isEquivalence
  ; trans         = transitive < Sto.trans
  ; compare       = trichotomous ≈ < Sto.compare
  ; <-resp-≈      = respects₂ < ≈ Sto.Eq.sym Sto.<-resp-≈
  }
  where module Sto = IsStrictTotalOrder sto

strictTotalOrder : StrictTotalOrder → StrictTotalOrder
strictTotalOrder O = record
  { _≈_                = flip₁ O._≈_
  ; _<_                = flip₁ O._<_
  ; isStrictTotalOrder = isStrictTotalOrder O.isStrictTotalOrder
  } where module O = StrictTotalOrder O
