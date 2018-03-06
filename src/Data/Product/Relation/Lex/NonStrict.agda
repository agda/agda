------------------------------------------------------------------------
-- The Agda standard library
--
-- Lexicographic products of binary relations
------------------------------------------------------------------------

-- The definition of lexicographic product used here is suitable if
-- the left-hand relation is a (non-strict) partial order.

module Data.Product.Relation.Lex.NonStrict where

open import Data.Product
open import Data.Sum
open import Level
open import Relation.Binary
open import Relation.Binary.Consequences
import Relation.Binary.NonStrictToStrict as Conv
open import Data.Product.Relation.Pointwise.NonDependent as Pointwise
  using (Pointwise)
import Data.Product.Relation.Lex.Strict as Strict

module _ {a₁ a₂ ℓ₁ ℓ₂} {A₁ : Set a₁} {A₂ : Set a₂} where

------------------------------------------------------------------------
-- A lexicographic ordering over products

  ×-Lex : (_≈₁_ _≤₁_ : Rel A₁ ℓ₁) (_≤₂_ : Rel A₂ ℓ₂) → Rel (A₁ × A₂) _
  ×-Lex _≈₁_ _≤₁_ _≤₂_ = Strict.×-Lex _≈₁_ (Conv._<_ _≈₁_ _≤₁_) _≤₂_

------------------------------------------------------------------------
-- Some properties which are preserved by ×-Lex (under certain
-- assumptions).

  ×-reflexive : ∀ _≈₁_ _≤₁_ {_≈₂_} _≤₂_ →
                _≈₂_ ⇒ _≤₂_ →
                (Pointwise _≈₁_ _≈₂_) ⇒ (×-Lex _≈₁_ _≤₁_ _≤₂_)
  ×-reflexive _≈₁_ _≤₁_ _≤₂_ refl₂ =
    Strict.×-reflexive _≈₁_ (Conv._<_ _≈₁_ _≤₁_) _≤₂_ refl₂

  ×-transitive : ∀ {_≈₁_ _≤₁_} → IsPartialOrder _≈₁_ _≤₁_ →
                 ∀ {_≤₂_} → Transitive _≤₂_ →
                 Transitive (×-Lex _≈₁_ _≤₁_ _≤₂_)
  ×-transitive {_≈₁_} {_≤₁_} po₁ {_≤₂_} trans₂ =
    Strict.×-transitive
      {_<₁_ = Conv._<_ _≈₁_ _≤₁_}
      isEquivalence (Conv.<-resp-≈ _ _ isEquivalence ≤-resp-≈)
      (Conv.trans _ _ po₁)
      {_≤₂_} trans₂
    where open IsPartialOrder po₁

  ×-antisymmetric :
    ∀ {_≈₁_ _≤₁_} → IsPartialOrder _≈₁_ _≤₁_ →
    ∀ {_≈₂_ _≤₂_} → Antisymmetric _≈₂_ _≤₂_ →
    Antisymmetric (Pointwise _≈₁_ _≈₂_) (×-Lex _≈₁_ _≤₁_ _≤₂_)
  ×-antisymmetric {_≈₁_} {_≤₁_}
                  po₁ {_≤₂_ = _≤₂_} antisym₂ =
    Strict.×-antisymmetric {_<₁_ = Conv._<_ _≈₁_ _≤₁_}
                           ≈-sym₁ irrefl₁ asym₁
                           {_≤₂_ = _≤₂_} antisym₂
    where
    open IsPartialOrder po₁
    open Eq renaming (refl to ≈-refl₁; sym to ≈-sym₁)

    irrefl₁ : Irreflexive _≈₁_ (Conv._<_ _≈₁_ _≤₁_)
    irrefl₁ = Conv.irrefl _≈₁_ _≤₁_

    asym₁ : Asymmetric (Conv._<_ _≈₁_ _≤₁_)
    asym₁ = trans∧irr⟶asym {_≈_ = _≈₁_}
                           ≈-refl₁ (Conv.trans _ _ po₁) irrefl₁

  ×-respects₂ :
    ∀ {_≈₁_ _≤₁_} → IsEquivalence _≈₁_ → _≤₁_ Respects₂ _≈₁_ →
    ∀ {_≈₂_ _≤₂_ : Rel A₂ ℓ₂} → _≤₂_ Respects₂ _≈₂_ →
    (×-Lex _≈₁_ _≤₁_ _≤₂_) Respects₂ (Pointwise _≈₁_ _≈₂_)
  ×-respects₂ eq₁ resp₁ resp₂ =
    Strict.×-respects₂ eq₁ (Conv.<-resp-≈ _ _ eq₁ resp₁) resp₂

  ×-decidable : ∀ {_≈₁_ _≤₁_} → Decidable _≈₁_ → Decidable _≤₁_ →
                ∀ {_≤₂_} → Decidable _≤₂_ →
                Decidable (×-Lex _≈₁_ _≤₁_ _≤₂_)
  ×-decidable dec-≈₁ dec-≤₁ dec-≤₂ =
    Strict.×-decidable dec-≈₁ (Conv.decidable _ _ dec-≈₁ dec-≤₁)
                       dec-≤₂

  ×-total : ∀ {_≈₁_ _≤₁_} → Symmetric _≈₁_ → Decidable _≈₁_ →
                            Antisymmetric _≈₁_ _≤₁_ → Total _≤₁_ →
            ∀ {_≤₂_} → Total _≤₂_ →
            Total (×-Lex _≈₁_ _≤₁_ _≤₂_)
  ×-total {_≈₁_} {_≤₁_} sym₁ dec₁ antisym₁ total₁ {_≤₂_} total₂ =
    total
    where
    tri₁ : Trichotomous _≈₁_ (Conv._<_ _≈₁_ _≤₁_)
    tri₁ = Conv.trichotomous _ _ sym₁ dec₁ antisym₁ total₁

    total : Total (×-Lex _≈₁_ _≤₁_ _≤₂_)
    total x y with tri₁ (proj₁ x) (proj₁ y)
    ... | tri< x₁<y₁ x₁≉y₁ x₁≯y₁ = inj₁ (inj₁ x₁<y₁)
    ... | tri> x₁≮y₁ x₁≉y₁ x₁>y₁ = inj₂ (inj₁ x₁>y₁)
    ... | tri≈ x₁≮y₁ x₁≈y₁ x₁≯y₁ with total₂ (proj₂ x) (proj₂ y)
    ...   | inj₁ x₂≤y₂ = inj₁ (inj₂ (x₁≈y₁ , x₂≤y₂))
    ...   | inj₂ x₂≥y₂ = inj₂ (inj₂ (sym₁ x₁≈y₁ , x₂≥y₂))

  -- Some collections of properties which are preserved by ×-Lex
  -- (under certain assumptions).

  ×-isPartialOrder :
    ∀ {_≈₁_ _≤₁_} → IsPartialOrder _≈₁_ _≤₁_ →
    ∀ {_≈₂_ _≤₂_} → IsPartialOrder _≈₂_ _≤₂_ →
    IsPartialOrder (Pointwise _≈₁_ _≈₂_) (×-Lex _≈₁_ _≤₁_ _≤₂_)
  ×-isPartialOrder {_≈₁_} {_≤₁_} po₁
                     {_≤₂_ = _≤₂_} po₂ = record
    { isPreorder = record
        { isEquivalence = Pointwise.×-isEquivalence
                            (isEquivalence po₁)
                            (isEquivalence po₂)
        ; reflexive     = ×-reflexive _≈₁_ _≤₁_ _≤₂_ (reflexive po₂)
        ; trans         = ×-transitive po₁ {_≤₂_ = _≤₂_} (trans po₂)
        }
    ; antisym = ×-antisymmetric {_≤₁_ = _≤₁_} po₁
                                {_≤₂_ = _≤₂_} (antisym po₂)
    }
    where open IsPartialOrder

  ×-isTotalOrder :
    ∀ {_≈₁_ _≤₁_} → Decidable _≈₁_ → IsTotalOrder _≈₁_ _≤₁_ →
    ∀ {_≈₂_ _≤₂_} → IsTotalOrder _≈₂_ _≤₂_ →
    IsTotalOrder (Pointwise _≈₁_ _≈₂_) (×-Lex _≈₁_ _≤₁_ _≤₂_)
  ×-isTotalOrder {_≤₁_ = _≤₁_} ≈₁-dec to₁ {_≤₂_ = _≤₂_} to₂ = record
    { isPartialOrder = ×-isPartialOrder
                         (isPartialOrder to₁) (isPartialOrder to₂)
    ; total          = ×-total {_≤₁_ = _≤₁_} (Eq.sym to₁) ≈₁-dec
                                             (antisym to₁) (total to₁)
                               {_≤₂_ = _≤₂_} (total to₂)
    }
    where open IsTotalOrder

  ×-isDecTotalOrder :
    ∀ {_≈₁_ _≤₁_} → IsDecTotalOrder _≈₁_ _≤₁_ →
    ∀ {_≈₂_ _≤₂_} → IsDecTotalOrder _≈₂_ _≤₂_ →
    IsDecTotalOrder (Pointwise _≈₁_ _≈₂_) (×-Lex _≈₁_ _≤₁_ _≤₂_)
  ×-isDecTotalOrder {_≤₁_ = _≤₁_} to₁ {_≤₂_ = _≤₂_} to₂ = record
    { isTotalOrder = ×-isTotalOrder (_≟_ to₁)
                                    (isTotalOrder to₁)
                                    (isTotalOrder to₂)
    ; _≟_          = Pointwise.×-decidable (_≟_ to₁) (_≟_ to₂)
    ; _≤?_         = ×-decidable (_≟_ to₁) (_≤?_ to₁) (_≤?_ to₂)
    }
    where open IsDecTotalOrder

------------------------------------------------------------------------
-- "Packages" can also be combined.

module _ {ℓ₁ ℓ₂ ℓ₃ ℓ₄} where

  ×-poset : Poset ℓ₁ ℓ₂ _ → Poset ℓ₃ ℓ₄ _ → Poset _ _ _
  ×-poset p₁ p₂ = record
    { isPartialOrder = ×-isPartialOrder
                         (isPartialOrder p₁) (isPartialOrder p₂)
    } where open Poset

  ×-totalOrder : DecTotalOrder ℓ₁ ℓ₂ _ → TotalOrder ℓ₃ ℓ₄ _ →
                 TotalOrder _ _ _
  ×-totalOrder t₁ t₂ = record
    { isTotalOrder = ×-isTotalOrder T₁._≟_ T₁.isTotalOrder T₂.isTotalOrder
    }
    where
    module T₁ = DecTotalOrder t₁
    module T₂ =    TotalOrder t₂

  ×-decTotalOrder : DecTotalOrder ℓ₁ ℓ₂ _ → DecTotalOrder ℓ₃ ℓ₄ _ →
                    DecTotalOrder _ _ _
  ×-decTotalOrder t₁ t₂ = record
    { isDecTotalOrder = ×-isDecTotalOrder
        (isDecTotalOrder t₁) (isDecTotalOrder t₂)
    } where open DecTotalOrder

------------------------------------------------------------------------
-- DEPRECATED NAMES
------------------------------------------------------------------------
-- Please use the new names as continuing support for the old names is
-- not guaranteed.

_×-isPartialOrder_  = ×-isPartialOrder
_×-isDecTotalOrder_ = ×-isDecTotalOrder
_×-poset_           = ×-poset
_×-totalOrder_      = ×-totalOrder
_×-decTotalOrder_   = ×-decTotalOrder

×-≈-respects₂       = ×-respects₂
