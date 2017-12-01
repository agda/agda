------------------------------------------------------------------------
-- The Agda standard library
--
-- Lexicographic products of binary relations
------------------------------------------------------------------------

-- The definition of lexicographic product used here is suitable if
-- the left-hand relation is a (non-strict) partial order.

module Data.Product.Relation.NonStrictLex where

open import Data.Product
open import Data.Sum
open import Level
open import Relation.Binary
open import Relation.Binary.Consequences
import Relation.Binary.NonStrictToStrict as Conv
open import Data.Product.Relation.Pointwise as Pointwise
  using (_×-Rel_)
import Data.Product.Relation.StrictLex as Strict

module _ {a₁ a₂ ℓ₁ ℓ₂} {A₁ : Set a₁} {A₂ : Set a₂} where

  ×-Lex : (_≈₁_ _≤₁_ : Rel A₁ ℓ₁) → (_≤₂_ : Rel A₂ ℓ₂) →
          Rel (A₁ × A₂) _
  ×-Lex _≈₁_ _≤₁_ _≤₂_ = Strict.×-Lex _≈₁_ (Conv._<_ _≈₁_ _≤₁_) _≤₂_

  -- Some properties which are preserved by ×-Lex (under certain
  -- assumptions).

  ×-reflexive : ∀ _≈₁_ _≤₁_ {_≈₂_} _≤₂_ →
                _≈₂_ ⇒ _≤₂_ → (_≈₁_ ×-Rel _≈₂_) ⇒ (×-Lex _≈₁_ _≤₁_ _≤₂_)
  ×-reflexive _≈₁_ _≤₁_ _≤₂_ refl₂ {x} {y} =
    Strict.×-reflexive _≈₁_ (Conv._<_ _≈₁_ _≤₁_) _≤₂_ refl₂ {x} {y}

  ×-transitive : ∀ {_≈₁_ _≤₁_} → IsPartialOrder _≈₁_ _≤₁_ →
                 ∀ {_≤₂_} → Transitive _≤₂_ →
                 Transitive (×-Lex _≈₁_ _≤₁_ _≤₂_)
  ×-transitive {_≈₁_ = _≈₁_} {_≤₁_ = _≤₁_} po₁ {_≤₂_ = _≤₂_} trans₂
               {x} {y} {z} =
    Strict.×-transitive
      {_<₁_ = Conv._<_ _≈₁_ _≤₁_}
      isEquivalence (Conv.<-resp-≈ _ _ isEquivalence ≤-resp-≈)
      (Conv.trans _ _ po₁)
      {_≤₂_ = _≤₂_} trans₂ {x} {y} {z}
    where open IsPartialOrder po₁

  ×-antisymmetric :
    ∀ {_≈₁_ _≤₁_} → IsPartialOrder _≈₁_ _≤₁_ →
    ∀ {_≈₂_ _≤₂_} → Antisymmetric _≈₂_ _≤₂_ →
    Antisymmetric (_≈₁_ ×-Rel _≈₂_) (×-Lex _≈₁_ _≤₁_ _≤₂_)
  ×-antisymmetric {_≈₁_ = _≈₁_} {_≤₁_ = _≤₁_}
                  po₁ {_≤₂_ = _≤₂_} antisym₂ {x} {y} =
    Strict.×-antisymmetric {_<₁_ = Conv._<_ _≈₁_ _≤₁_}
                           ≈-sym₁ irrefl₁ asym₁
                           {_≤₂_ = _≤₂_} antisym₂ {x} {y}
    where
    open IsPartialOrder po₁
    open Eq renaming (refl to ≈-refl₁; sym to ≈-sym₁)

    irrefl₁ : Irreflexive _≈₁_ (Conv._<_ _≈₁_ _≤₁_)
    irrefl₁ = Conv.irrefl _≈₁_ _≤₁_

    asym₁ : Asymmetric (Conv._<_ _≈₁_ _≤₁_)
    asym₁ = trans∧irr⟶asym {_≈_ = _≈₁_}
                           ≈-refl₁ (Conv.trans _ _ po₁) irrefl₁

  ×-≈-respects₂ :
    ∀ {_≈₁_ _≤₁_} → IsEquivalence _≈₁_ → _≤₁_ Respects₂ _≈₁_ →
    ∀ {_≈₂_ _≤₂_ : Rel A₂ ℓ₂} → _≤₂_ Respects₂ _≈₂_ →
    (×-Lex _≈₁_ _≤₁_ _≤₂_) Respects₂ (_≈₁_ ×-Rel _≈₂_)
  ×-≈-respects₂ eq₁ resp₁ resp₂ =
    Strict.×-≈-respects₂ eq₁ (Conv.<-resp-≈ _ _ eq₁ resp₁) resp₂

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
  ×-total {_≈₁_ = _≈₁_} {_≤₁_ = _≤₁_} sym₁ dec₁ antisym₁ total₁
                        {_≤₂_ = _≤₂_} total₂ = total
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

  _×-isPartialOrder_ :
    ∀ {_≈₁_ _≤₁_} → IsPartialOrder _≈₁_ _≤₁_ →
    ∀ {_≈₂_ _≤₂_} → IsPartialOrder _≈₂_ _≤₂_ →
    IsPartialOrder (_≈₁_ ×-Rel _≈₂_) (×-Lex _≈₁_ _≤₁_ _≤₂_)
  _×-isPartialOrder_ {_≈₁_ = _≈₁_} {_≤₁_ = _≤₁_} po₁
                     {_≤₂_ = _≤₂_} po₂ = record
    { isPreorder = record
        { isEquivalence = Pointwise._×-isEquivalence_
                            (isEquivalence po₁)
                            (isEquivalence po₂)
        ; reflexive     = λ {x y} →
                          ×-reflexive _≈₁_ _≤₁_ _≤₂_ (reflexive po₂)
                                      {x} {y}
        ; trans         = λ {x y z} →
                          ×-transitive po₁ {_≤₂_ = _≤₂_} (trans po₂)
                                       {x} {y} {z}
        }
    ; antisym = λ {x y} →
                ×-antisymmetric {_≤₁_ = _≤₁_} po₁
                                {_≤₂_ = _≤₂_} (antisym po₂) {x} {y}
    }
    where open IsPartialOrder

  ×-isTotalOrder :
    ∀ {_≈₁_ _≤₁_} → Decidable _≈₁_ → IsTotalOrder _≈₁_ _≤₁_ →
    ∀ {_≈₂_ _≤₂_} → IsTotalOrder _≈₂_ _≤₂_ →
    IsTotalOrder (_≈₁_ ×-Rel _≈₂_) (×-Lex _≈₁_ _≤₁_ _≤₂_)
  ×-isTotalOrder {_≤₁_ = _≤₁_} ≈₁-dec to₁ {_≤₂_ = _≤₂_} to₂ = record
    { isPartialOrder = isPartialOrder to₁ ×-isPartialOrder
                       isPartialOrder to₂
    ; total          = ×-total {_≤₁_ = _≤₁_} (Eq.sym to₁) ≈₁-dec
                                             (antisym to₁) (total to₁)
                               {_≤₂_ = _≤₂_} (total to₂)
    }
    where open IsTotalOrder

  _×-isDecTotalOrder_ :
    ∀ {_≈₁_ _≤₁_} → IsDecTotalOrder _≈₁_ _≤₁_ →
    ∀ {_≈₂_ _≤₂_} → IsDecTotalOrder _≈₂_ _≤₂_ →
    IsDecTotalOrder (_≈₁_ ×-Rel _≈₂_) (×-Lex _≈₁_ _≤₁_ _≤₂_)
  _×-isDecTotalOrder_ {_≤₁_ = _≤₁_} to₁ {_≤₂_ = _≤₂_} to₂ = record
    { isTotalOrder = ×-isTotalOrder (_≟_ to₁)
                                    (isTotalOrder to₁)
                                    (isTotalOrder to₂)
    ; _≟_          = Pointwise._×-decidable_ (_≟_ to₁) (_≟_ to₂)
    ; _≤?_         = ×-decidable (_≟_ to₁) (_≤?_ to₁) (_≤?_ to₂)
    }
    where open IsDecTotalOrder

-- "Packages" (e.g. posets) can also be combined.

_×-poset_ :
  ∀ {p₁ p₂ p₃ p₄} → Poset p₁ p₂ _ → Poset p₃ p₄ _ → Poset _ _ _
p₁ ×-poset p₂ = record
  { isPartialOrder = isPartialOrder p₁ ×-isPartialOrder
                     isPartialOrder p₂
  } where open Poset

_×-totalOrder_ :
  ∀ {d₁ d₂ t₃ t₄} →
  DecTotalOrder d₁ d₂ _ → TotalOrder t₃ t₄ _ → TotalOrder _ _ _
t₁ ×-totalOrder t₂ = record
  { isTotalOrder = ×-isTotalOrder T₁._≟_ T₁.isTotalOrder T₂.isTotalOrder
  }
  where
  module T₁ = DecTotalOrder t₁
  module T₂ =    TotalOrder t₂

_×-decTotalOrder_ :
  ∀ {d₁ d₂ d₃ d₄} →
  DecTotalOrder d₁ d₂ _ → DecTotalOrder d₃ d₄ _ → DecTotalOrder _ _ _
t₁ ×-decTotalOrder t₂ = record
  { isDecTotalOrder = isDecTotalOrder t₁ ×-isDecTotalOrder
                      isDecTotalOrder t₂
  } where open DecTotalOrder
