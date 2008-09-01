------------------------------------------------------------------------
-- Many properties which hold for _∼_ also hold for _∼_ on₁ f
------------------------------------------------------------------------

open import Relation.Binary

module Relation.Binary.On {A B : Set} (f : B -> A) where

open import Data.Function
open import Data.Product

implies : forall ≈ ∼ -> ≈ ⇒ ∼ -> (≈ on₁ f) ⇒ (∼ on₁ f)
implies _ _ impl = impl

reflexive : forall ∼ -> Reflexive ∼ -> Reflexive (∼ on₁ f)
reflexive _ refl = refl

irreflexive : forall ≈ ∼ ->
              Irreflexive ≈ ∼ -> Irreflexive (≈ on₁ f) (∼ on₁ f)
irreflexive _ _ irrefl = irrefl

symmetric : forall ∼ -> Symmetric ∼ -> Symmetric (∼ on₁ f)
symmetric _ sym = sym

transitive : forall ∼ -> Transitive ∼ -> Transitive (∼ on₁ f)
transitive _ trans = trans

antisymmetric : forall ≈ ≤ ->
                Antisymmetric ≈ ≤ -> Antisymmetric (≈ on₁ f) (≤ on₁ f)
antisymmetric _ _ antisym = antisym

asymmetric : forall < -> Asymmetric < -> Asymmetric (< on₁ f)
asymmetric _ asym = asym

respects : forall ∼ P ->
           ∼ Respects P -> (∼ on₁ f) Respects (\x -> P (f x))
respects _ _ resp = resp

respects₂ : forall ∼₁ ∼₂ ->
            ∼₁ Respects₂ ∼₂ -> (∼₁ on₁ f) Respects₂ (∼₂ on₁ f)
respects₂ _ _ (resp₁ , resp₂) =
  ((\{_} {_} {_} -> resp₁) , \{_} {_} {_} -> resp₂)

decidable : forall ∼ -> Decidable ∼ -> Decidable (∼ on₁ f)
decidable _ dec = \x y -> dec (f x) (f y)

total : forall ∼ -> Total ∼ -> Total (∼ on₁ f)
total _ tot = \x y -> tot (f x) (f y)

trichotomous : forall ≈ < ->
               Trichotomous ≈ < -> Trichotomous (≈ on₁ f) (< on₁ f)
trichotomous _ _ compare = \x y -> compare (f x) (f y)

isEquivalence : forall {≈} ->
                IsEquivalence ≈ -> IsEquivalence (≈ on₁ f)
isEquivalence {≈} eq = record
  { refl  = reflexive  ≈ Eq.refl
  ; sym   = symmetric  ≈ Eq.sym
  ; trans = transitive ≈ Eq.trans
  }
  where module Eq = IsEquivalence eq

isPreorder : forall {≈ ∼} ->
             IsPreorder ≈ ∼ -> IsPreorder (≈ on₁ f) (∼ on₁ f)
isPreorder {≈} {∼} pre = record
  { isEquivalence = isEquivalence Pre.isEquivalence
  ; reflexive     = implies ≈ ∼ Pre.reflexive
  ; trans         = transitive ∼ Pre.trans
  ; ≈-resp-∼      = respects₂ ≈ ∼ Pre.≈-resp-∼
  }
  where module Pre = IsPreorder pre

isDecEquivalence : forall {≈} ->
                   IsDecEquivalence ≈ -> IsDecEquivalence (≈ on₁ f)
isDecEquivalence {≈} dec = record
  { isEquivalence = isEquivalence Dec.isEquivalence
  ; _≟_           = decidable ≈ Dec._≟_
  }
  where module Dec = IsDecEquivalence dec

isPartialOrder : forall {≈ ≤} ->
                 IsPartialOrder ≈ ≤ ->
                 IsPartialOrder (≈ on₁ f) (≤ on₁ f)
isPartialOrder {≈} {≤} po = record
  { isPreorder = isPreorder Po.isPreorder
  ; antisym    = antisymmetric ≈ ≤ Po.antisym
  }
  where module Po = IsPartialOrder po

isStrictPartialOrder : forall {≈ <} ->
               IsStrictPartialOrder ≈ < ->
               IsStrictPartialOrder (≈ on₁ f) (< on₁ f)
isStrictPartialOrder {≈} {<} spo = record
  { isEquivalence = isEquivalence Spo.isEquivalence
  ; irrefl        = irreflexive ≈ < Spo.irrefl
  ; trans         = transitive < Spo.trans
  ; ≈-resp-<      = respects₂ ≈ < Spo.≈-resp-<
  }
  where module Spo = IsStrictPartialOrder spo

isTotalOrder : forall {≈ ≤} ->
               IsTotalOrder ≈ ≤ ->
               IsTotalOrder (≈ on₁ f) (≤ on₁ f)
isTotalOrder {≈} {≤} to = record
  { isPartialOrder = isPartialOrder To.isPartialOrder
  ; total          = total ≤ To.total
  }
  where module To = IsTotalOrder to

isDecTotalOrder : forall {≈ ≤} ->
                  IsDecTotalOrder ≈ ≤ ->
                  IsDecTotalOrder (≈ on₁ f) (≤ on₁ f)
isDecTotalOrder {≈} {≤} dec = record
  { isTotalOrder = isTotalOrder Dec.isTotalOrder
  ; _≟_          = decidable ≈ Dec._≟_
  ; _≤?_         = decidable ≤ Dec._≤?_
  }
  where module Dec = IsDecTotalOrder dec

isStrictTotalOrder : forall {≈ <} ->
                  IsStrictTotalOrder ≈ < ->
                  IsStrictTotalOrder (≈ on₁ f) (< on₁ f)
isStrictTotalOrder {≈} {<} sto = record
  { isEquivalence = isEquivalence Sto.isEquivalence
  ; trans         = transitive < Sto.trans
  ; compare       = trichotomous ≈ < Sto.compare
  ; ≈-resp-<      = respects₂ ≈ < Sto.≈-resp-<
  }
  where module Sto = IsStrictTotalOrder sto
