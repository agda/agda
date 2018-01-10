------------------------------------------------------------------------
-- The Agda standard library
--
-- Conversion of ≤ to <, along with a number of properties
------------------------------------------------------------------------

-- Possible TODO: Prove that a conversion ≤ → < → ≤ returns a
-- relation equivalent to the original one (and similarly for
-- < → ≤ → <).

open import Relation.Binary

module Relation.Binary.NonStrictToStrict
         {a ℓ₁ ℓ₂} {A : Set a}
         (_≈_ : Rel A ℓ₁) (_≤_ : Rel A ℓ₂)
         where

open import Relation.Nullary
open import Relation.Binary.Consequences
open import Function
open import Data.Product
open import Data.Sum

------------------------------------------------------------------------
-- Conversion

-- _≤_ can be turned into _<_ as follows:

_<_ : Rel A _
x < y = (x ≤ y) × ¬ (x ≈ y)

------------------------------------------------------------------------
-- The converted relations have certain properties
-- (if the original relations have certain other properties)

irrefl : Irreflexive _≈_ _<_
irrefl x≈y (_ , x≉y) = x≉y x≈y

trans : IsPartialOrder _≈_ _≤_ → Transitive _<_
trans po (x≤y , x≉y) (y≤z , y≉z) =
  (PO.trans x≤y y≤z , x≉y ∘ lemma x≤y y≤z)
  where
  module PO = IsPartialOrder po

  lemma : ∀ {x y z} → x ≤ y → y ≤ z → x ≈ z → x ≈ y
  lemma x≤y y≤z x≈z =
    PO.antisym x≤y $ PO.trans y≤z (PO.reflexive $ PO.Eq.sym x≈z)

antisym⟶asym : Antisymmetric _≈_ _≤_ → Asymmetric _<_
antisym⟶asym antisym (x≤y , x≉y) (y≤x , _) = x≉y (antisym x≤y y≤x)

<-resp-≈ : IsEquivalence _≈_ → _≤_ Respects₂ _≈_ → _<_ Respects₂ _≈_
<-resp-≈ eq ≤-resp-≈ =
  (λ {x y' y} y'≈y x<y' →
    ( proj₁ ≤-resp-≈ y'≈y (proj₁ x<y')
    , λ x≈y → proj₂ x<y' (Eq.trans x≈y (Eq.sym y'≈y))
    )
  ) ,
  (λ {y x' x} x'≈x x'<y →
    ( proj₂ ≤-resp-≈ x'≈x (proj₁ x'<y)
    , λ x≈y → proj₂ x'<y (Eq.trans x'≈x x≈y)
    ))
  where module Eq = IsEquivalence eq

trichotomous : Symmetric _≈_ → Decidable _≈_ →
               Antisymmetric _≈_ _≤_ → Total _≤_ →
               Trichotomous _≈_ _<_
trichotomous ≈-sym ≈-dec antisym total x y with ≈-dec x y
... | yes x≈y = tri≈ (irrefl x≈y) x≈y (irrefl (≈-sym x≈y))
... | no  x≉y with total x y
...   | inj₁ x≤y = tri< (x≤y , x≉y) x≉y
                        (x≉y ∘ antisym x≤y ∘ proj₁)
...   | inj₂ x≥y = tri> (x≉y ∘ flip antisym x≥y ∘ proj₁) x≉y
                        (x≥y , x≉y ∘ ≈-sym)

decidable : Decidable _≈_ → Decidable _≤_ → Decidable _<_
decidable ≈-dec ≤-dec x y with ≈-dec x y | ≤-dec x y
... | yes x≈y | _       = no (flip proj₂ x≈y)
... | no  x≉y | yes x≤y = yes (x≤y , x≉y)
... | no  x≉y | no  x≰y = no (x≰y ∘ proj₁)

isPartialOrder⟶isStrictPartialOrder :
  IsPartialOrder _≈_ _≤_ → IsStrictPartialOrder _≈_ _<_
isPartialOrder⟶isStrictPartialOrder po = record
  { isEquivalence = PO.isEquivalence
  ; irrefl        = irrefl
  ; trans         = trans po
  ; <-resp-≈      = <-resp-≈ PO.isEquivalence PO.≤-resp-≈
  } where module PO = IsPartialOrder po

isTotalOrder⟶isStrictTotalOrder :
  Decidable _≈_ → IsTotalOrder _≈_ _≤_ → IsStrictTotalOrder _≈_ _<_
isTotalOrder⟶isStrictTotalOrder dec-≈ tot = record
  { isEquivalence = TO.isEquivalence
  ; trans         = trans TO.isPartialOrder
  ; compare       = trichotomous TO.Eq.sym dec-≈ TO.antisym TO.total
  } where module TO = IsTotalOrder tot

isDecTotalOrder⟶isStrictTotalOrder :
  IsDecTotalOrder _≈_ _≤_ → IsStrictTotalOrder _≈_ _<_
isDecTotalOrder⟶isStrictTotalOrder dtot =
  isTotalOrder⟶isStrictTotalOrder DTO._≟_ DTO.isTotalOrder
  where module DTO = IsDecTotalOrder dtot
