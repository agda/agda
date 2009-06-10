------------------------------------------------------------------------
-- Lexicographic products of binary relations
------------------------------------------------------------------------

-- The definition of lexicographic product used here is suitable if
-- the left-hand relation is a (non-strict) partial order.

module Relation.Binary.Product.NonStrictLex where

open import Data.Product
open import Data.Sum
open import Relation.Binary
open import Relation.Binary.Consequences
import Relation.Binary.NonStrictToStrict as Conv
open import Relation.Binary.Product.Pointwise as Pointwise
  using (_×-Rel_)
import Relation.Binary.Product.StrictLex as Strict

private
 module Dummy {a₁ a₂ : Set} where

  ×-Lex : (≈₁ ≤₁ : Rel a₁) → (≤₂ : Rel a₂) → Rel (a₁ × a₂)
  ×-Lex ≈₁ ≤₁ ≤₂ = Strict.×-Lex ≈₁ (Conv._<_ ≈₁ ≤₁) ≤₂

  -- Some properties which are preserved by ×-Lex (under certain
  -- assumptions).

  ×-reflexive : ∀ ≈₁ ≤₁ {≈₂} ≤₂ →
                ≈₂ ⇒ ≤₂ → (≈₁ ×-Rel ≈₂) ⇒ (×-Lex ≈₁ ≤₁ ≤₂)
  ×-reflexive ≈₁ ≤₁ ≤₂ refl₂ {x} {y} =
    Strict.×-reflexive ≈₁ (Conv._<_ ≈₁ ≤₁) ≤₂ refl₂ {x} {y}

  ×-transitive : ∀ {≈₁ ≤₁} → IsPartialOrder ≈₁ ≤₁ →
                 ∀ {≤₂} → Transitive ≤₂ →
                 Transitive (×-Lex ≈₁ ≤₁ ≤₂)
  ×-transitive {≈₁ = ≈₁} {≤₁ = ≤₁} po₁ {≤₂ = ≤₂} trans₂
               {x} {y} {z} =
    Strict.×-transitive
      {<₁ = Conv._<_ ≈₁ ≤₁}
      isEquivalence (Conv.<-resp-≈ _ _ isEquivalence ≤-resp-≈)
      (Conv.trans _ _ po₁)
      {≤₂ = ≤₂} trans₂ {x} {y} {z}
    where open IsPartialOrder po₁

  ×-antisymmetric : ∀ {≈₁ ≤₁} → IsPartialOrder ≈₁ ≤₁ →
                    ∀ {≈₂ ≤₂} → Antisymmetric ≈₂ ≤₂ →
                    Antisymmetric (≈₁ ×-Rel ≈₂) (×-Lex ≈₁ ≤₁ ≤₂)
  ×-antisymmetric {≈₁ = ≈₁} {≤₁ = ≤₁} po₁ {≤₂ = ≤₂} antisym₂
                  {x} {y} =
    Strict.×-antisymmetric {<₁ = Conv._<_ ≈₁ ≤₁} ≈-sym₁ irrefl₁ asym₁
                           {≤₂ = ≤₂} antisym₂ {x} {y}
    where
    open IsPartialOrder po₁
    open Eq renaming (refl to ≈-refl₁; sym to ≈-sym₁)

    irrefl₁ : Irreflexive ≈₁ (Conv._<_ ≈₁ ≤₁)
    irrefl₁ = Conv.irrefl ≈₁ ≤₁

    asym₁ : Asymmetric (Conv._<_ ≈₁ ≤₁)
    asym₁ = trans∧irr⟶asym {≈ = ≈₁}
                           ≈-refl₁ (Conv.trans _ _ po₁) irrefl₁

  ×-≈-respects₂ : ∀ {≈₁ ≤₁} → IsEquivalence ≈₁ → ≤₁ Respects₂ ≈₁ →
                  ∀ {≈₂ ≤₂} → ≤₂ Respects₂ ≈₂ →
                  (×-Lex ≈₁ ≤₁ ≤₂) Respects₂ (≈₁ ×-Rel ≈₂)
  ×-≈-respects₂ eq₁ resp₁ resp₂ =
    Strict.×-≈-respects₂ eq₁ (Conv.<-resp-≈ _ _ eq₁ resp₁) resp₂

  ×-decidable : ∀ {≈₁ ≤₁} → Decidable ≈₁ → Decidable ≤₁ →
                ∀ {≤₂} → Decidable ≤₂ →
                Decidable (×-Lex ≈₁ ≤₁ ≤₂)
  ×-decidable dec-≈₁ dec-≤₁ dec-≤₂ =
    Strict.×-decidable dec-≈₁ (Conv.decidable _ _ dec-≈₁ dec-≤₁)
                       dec-≤₂

  ×-total : ∀ {≈₁ ≤₁} → Symmetric ≈₁ → Decidable ≈₁ →
                        Antisymmetric ≈₁ ≤₁ → Total ≤₁ →
            ∀ {≤₂} → Total ≤₂ →
            Total (×-Lex ≈₁ ≤₁ ≤₂)
  ×-total {≈₁ = ≈₁} {≤₁ = ≤₁} sym₁ dec₁ antisym₁ total₁
                    {≤₂ = ≤₂} total₂ = total
    where
    tri₁ : Trichotomous ≈₁ (Conv._<_ ≈₁ ≤₁)
    tri₁ = Conv.trichotomous _ _ sym₁ dec₁ antisym₁ total₁

    total : Total (×-Lex ≈₁ ≤₁ ≤₂)
    total x y with tri₁ (proj₁ x) (proj₁ y)
    ... | tri< x₁<y₁ x₁≉y₁ x₁≯y₁ = inj₁ (inj₁ x₁<y₁)
    ... | tri> x₁≮y₁ x₁≉y₁ x₁>y₁ = inj₂ (inj₁ x₁>y₁)
    ... | tri≈ x₁≮y₁ x₁≈y₁ x₁≯y₁ with total₂ (proj₂ x) (proj₂ y)
    ...   | inj₁ x₂≤y₂ = inj₁ (inj₂ (x₁≈y₁ , x₂≤y₂))
    ...   | inj₂ x₂≥y₂ = inj₂ (inj₂ (sym₁ x₁≈y₁ , x₂≥y₂))

  -- Some collections of properties which are preserved by ×-Lex
  -- (under certain assumptions).

  _×-isPartialOrder_ : ∀ {≈₁ ≤₁} → IsPartialOrder ≈₁ ≤₁ →
                       ∀ {≈₂ ≤₂} → IsPartialOrder ≈₂ ≤₂ →
                       IsPartialOrder (≈₁ ×-Rel ≈₂) (×-Lex ≈₁ ≤₁ ≤₂)
  _×-isPartialOrder_ {≈₁ = ≈₁} {≤₁ = ≤₁} po₁ {≤₂ = ≤₂} po₂ = record
    { isPreorder = record
        { isEquivalence = Pointwise._×-isEquivalence_
                            (isEquivalence po₁)
                            (isEquivalence po₂)
        ; reflexive     = λ {x y} →
                          ×-reflexive ≈₁ ≤₁ ≤₂ (reflexive po₂) {x} {y}
        ; trans         = λ {x y z} →
                          ×-transitive po₁ {≤₂ = ≤₂} (trans po₂)
                                       {x} {y} {z}
        ; ∼-resp-≈      = ×-≈-respects₂ (isEquivalence po₁)
                                        (≤-resp-≈ po₁)
                                        (≤-resp-≈ po₂)
        }
    ; antisym = λ {x y} →
                ×-antisymmetric {≤₁ = ≤₁} po₁
                                {≤₂ = ≤₂} (antisym po₂) {x} {y}
    }
    where open IsPartialOrder

  ×-isTotalOrder : ∀ {≈₁ ≤₁} → Decidable ≈₁ → IsTotalOrder ≈₁ ≤₁ →
                   ∀ {≈₂ ≤₂} → IsTotalOrder ≈₂ ≤₂ →
                   IsTotalOrder (≈₁ ×-Rel ≈₂) (×-Lex ≈₁ ≤₁ ≤₂)
  ×-isTotalOrder {≤₁ = ≤₁} ≈₁-dec to₁ {≤₂ = ≤₂} to₂ = record
    { isPartialOrder = isPartialOrder to₁ ×-isPartialOrder
                       isPartialOrder to₂
    ; total          = ×-total {≤₁ = ≤₁} (Eq.sym to₁) ≈₁-dec
                                         (antisym to₁) (total to₁)
                               {≤₂ = ≤₂} (total to₂)
    }
    where open IsTotalOrder

  _×-isDecTotalOrder_ : ∀ {≈₁ ≤₁} → IsDecTotalOrder ≈₁ ≤₁ →
                        ∀ {≈₂ ≤₂} → IsDecTotalOrder ≈₂ ≤₂ →
                        IsDecTotalOrder (≈₁ ×-Rel ≈₂) (×-Lex ≈₁ ≤₁ ≤₂)
  _×-isDecTotalOrder_ {≤₁ = ≤₁} to₁ {≤₂ = ≤₂} to₂ = record
    { isTotalOrder = ×-isTotalOrder (_≟_ to₁)
                                    (isTotalOrder to₁)
                                    (isTotalOrder to₂)
    ; _≟_          = Pointwise._×-decidable_ (_≟_ to₁) (_≟_ to₂)
    ; _≤?_         = ×-decidable (_≟_ to₁) (_≤?_ to₁) (_≤?_ to₂)
    }
    where open IsDecTotalOrder

open Dummy public

-- "Packages" (e.g. posets) can also be combined.

_×-poset_ : Poset → Poset → Poset
p₁ ×-poset p₂ = record
  { isPartialOrder = isPartialOrder p₁ ×-isPartialOrder
                     isPartialOrder p₂
  } where open Poset

_×-totalOrder_ : DecTotalOrder → TotalOrder → TotalOrder
t₁ ×-totalOrder t₂ = record
  { isTotalOrder = ×-isTotalOrder T₁._≟_ T₁.isTotalOrder T₂.isTotalOrder
  }
  where
  module T₁ = DecTotalOrder t₁
  module T₂ =    TotalOrder t₂

_×-decTotalOrder_ : DecTotalOrder → DecTotalOrder → DecTotalOrder
t₁ ×-decTotalOrder t₂ = record
  { isDecTotalOrder = isDecTotalOrder t₁ ×-isDecTotalOrder
                      isDecTotalOrder t₂
  } where open DecTotalOrder
