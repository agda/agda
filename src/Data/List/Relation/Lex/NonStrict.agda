------------------------------------------------------------------------
-- The Agda standard library
--
-- Lexicographic ordering of lists
------------------------------------------------------------------------

-- The definitions of lexicographic orderings used here is suitable if
-- the argument order is a (non-strict) partial order.

module Data.List.Relation.Lex.NonStrict where

open import Data.Empty using (⊥)
open import Function
open import Data.Unit.Base using (⊤; tt)
open import Data.Product
open import Data.List.Base
open import Data.List.Relation.Pointwise using (Pointwise; [])
import Data.List.Relation.Lex.Strict as Strict
open import Level
open import Relation.Nullary
open import Relation.Binary
import Relation.Binary.NonStrictToStrict as Conv

------------------------------------------------------------------------
-- Publically re-export definitions from Core

open import Data.List.Relation.Lex.Core as Core public
  using (base; halt; this; next; ¬≤-this; ¬≤-next)

------------------------------------------------------------------------
-- Strict lexicographic ordering.

module _ {a ℓ₁ ℓ₂} {A : Set a} where

  Lex-< : (_≈_ : Rel A ℓ₁) (_≼_ : Rel A ℓ₂) → Rel (List A) (ℓ₁ ⊔ ℓ₂)
  Lex-< _≈_ _≼_ = Core.Lex ⊥ _≈_ (Conv._<_ _≈_ _≼_)

  -- Properties

  module _ {_≈_ : Rel A ℓ₁} {_≼_ : Rel A ℓ₂} where

    private
      _≋_ = Pointwise _≈_
      _<_ = Lex-< _≈_ _≼_

    <-irreflexive : Irreflexive _≋_ _<_
    <-irreflexive = Strict.<-irreflexive (Conv.irrefl _≈_ _≼_)

    <-asymmetric : IsEquivalence _≈_ → _≼_ Respects₂ _≈_ →
                   Antisymmetric _≈_ _≼_ → Asymmetric _<_
    <-asymmetric eq resp antisym  =
      Strict.<-asymmetric sym (Conv.<-resp-≈ _ _ eq resp)
                        (Conv.antisym⟶asym _≈_ _ antisym)
                        where open IsEquivalence eq

    <-antisymmetric : Symmetric _≈_ → Antisymmetric _≈_ _≼_ →
                      Antisymmetric _≋_ _<_
    <-antisymmetric sym antisym =
      Core.antisymmetric sym
        (Conv.irrefl _≈_ _≼_)
        (Conv.antisym⟶asym _ _≼_ antisym)

    <-transitive : IsPartialOrder _≈_ _≼_ → Transitive _<_
    <-transitive po =
      Core.transitive isEquivalence
        (Conv.<-resp-≈ _ _ isEquivalence ≤-resp-≈)
        (Conv.trans _ _≼_ po)
      where open IsPartialOrder po

    <-resp₂ : IsEquivalence _≈_ → _≼_ Respects₂ _≈_ → _<_ Respects₂ _≋_
    <-resp₂ eq resp = Core.respects₂ eq (Conv.<-resp-≈ _ _ eq resp)

    <-compare : Symmetric _≈_ → Decidable _≈_ → Antisymmetric _≈_ _≼_ →
                Total _≼_ → Trichotomous _≋_ _<_
    <-compare sym _≟_ antisym tot =
      Strict.<-compare sym (Conv.trichotomous _ _ sym _≟_ antisym tot)

    <-decidable : Decidable _≈_ → Decidable _≼_ → Decidable _<_
    <-decidable _≟_ _≼?_ =
      Core.decidable (no id) _≟_ (Conv.decidable _ _ _≟_ _≼?_)

    <-isStrictPartialOrder : IsPartialOrder _≈_ _≼_ →
                             IsStrictPartialOrder _≋_ _<_
    <-isStrictPartialOrder po =
      Strict.<-isStrictPartialOrder
        (Conv.isPartialOrder⟶isStrictPartialOrder _ _ po)

    <-isStrictTotalOrder : Decidable _≈_ → IsTotalOrder _≈_ _≼_ →
                           IsStrictTotalOrder _≋_ _<_
    <-isStrictTotalOrder dec tot =
      Strict.<-isStrictTotalOrder
        (Conv.isTotalOrder⟶isStrictTotalOrder _ _ dec tot)

<-strictPartialOrder : ∀ {a ℓ₁ ℓ₂} → Poset a ℓ₁ ℓ₂ →
                       StrictPartialOrder _ _ _
<-strictPartialOrder po = record
  { isStrictPartialOrder = <-isStrictPartialOrder isPartialOrder
  } where open Poset po

<-strictTotalOrder : ∀ {a ℓ₁ ℓ₂} → DecTotalOrder a ℓ₁ ℓ₂ →
                     StrictTotalOrder _ _ _
<-strictTotalOrder dtot = record
  { isStrictTotalOrder = <-isStrictTotalOrder _≟_ isTotalOrder
  } where open IsDecTotalOrder (DecTotalOrder.isDecTotalOrder dtot)

------------------------------------------------------------------------
-- Non-strict lexicographic ordering.

module _ {a ℓ₁ ℓ₂} {A : Set a} where

  Lex-≤ : (_≈_ : Rel A ℓ₁) (_≼_ : Rel A ℓ₂) → Rel (List A) (ℓ₁ ⊔ ℓ₂)
  Lex-≤ _≈_ _≼_ = Core.Lex ⊤ _≈_ (Conv._<_ _≈_ _≼_)

  ≤-reflexive : ∀ _≈_ _≼_ → Pointwise _≈_ ⇒ Lex-≤ _≈_ _≼_
  ≤-reflexive _≈_ _≼_ = Strict.≤-reflexive _≈_ (Conv._<_ _≈_ _≼_)

  -- Properties
  module _ {_≈_ : Rel A ℓ₁} {_≼_ : Rel A ℓ₂} where

    private
      _≋_ = Pointwise _≈_
      _≤_ = Lex-≤ _≈_ _≼_

    ≤-antisymmetric : Symmetric _≈_ → Antisymmetric _≈_ _≼_ →
                      Antisymmetric _≋_ _≤_
    ≤-antisymmetric sym antisym =
      Core.antisymmetric sym
        (Conv.irrefl _≈_ _≼_)
        (Conv.antisym⟶asym _ _≼_ antisym)

    ≤-transitive : IsPartialOrder _≈_ _≼_ → Transitive _≤_
    ≤-transitive po =
      Core.transitive isEquivalence
        (Conv.<-resp-≈ _ _ isEquivalence ≤-resp-≈)
        (Conv.trans _ _≼_ po)
      where open IsPartialOrder po

    ≤-resp₂ : IsEquivalence _≈_ → _≼_ Respects₂ _≈_ → _≤_ Respects₂ _≋_
    ≤-resp₂ eq resp = Core.respects₂ eq (Conv.<-resp-≈ _ _ eq resp)

    ≤-decidable : Decidable _≈_ → Decidable _≼_ → Decidable _≤_
    ≤-decidable _≟_ _≼?_ =
      Core.decidable (yes tt) _≟_ (Conv.decidable _ _ _≟_ _≼?_)

    ≤-total : Symmetric _≈_ → Decidable _≈_ → Antisymmetric _≈_ _≼_ →
              Total _≼_ → Total _≤_
    ≤-total sym dec-≈ antisym tot =
      Strict.≤-total sym (Conv.trichotomous _ _ sym dec-≈ antisym tot)

    ≤-isPreorder : IsPartialOrder _≈_ _≼_ → IsPreorder _≋_ _≤_
    ≤-isPreorder po =
      Strict.≤-isPreorder
        isEquivalence (Conv.trans _ _ po)
        (Conv.<-resp-≈ _ _ isEquivalence ≤-resp-≈)
      where open IsPartialOrder po

    ≤-isPartialOrder : IsPartialOrder _≈_ _≼_ → IsPartialOrder _≋_ _≤_
    ≤-isPartialOrder po =
      Strict.≤-isPartialOrder
        (Conv.isPartialOrder⟶isStrictPartialOrder _ _ po)

    ≤-isTotalOrder : Decidable _≈_ → IsTotalOrder _≈_ _≼_ →
                     IsTotalOrder _≋_ _≤_
    ≤-isTotalOrder dec tot =
      Strict.≤-isTotalOrder
        (Conv.isTotalOrder⟶isStrictTotalOrder _ _ dec tot)

    ≤-isDecTotalOrder : IsDecTotalOrder _≈_ _≼_ →
                        IsDecTotalOrder _≋_ _≤_
    ≤-isDecTotalOrder dtot =
      Strict.≤-isDecTotalOrder
        (Conv.isDecTotalOrder⟶isStrictTotalOrder _ _ dtot)

≤-preorder : ∀ {a ℓ₁ ℓ₂} → Poset a ℓ₁ ℓ₂ → Preorder _ _ _
≤-preorder po = record
  { isPreorder = ≤-isPreorder isPartialOrder
  } where open Poset po

≤-partialOrder : ∀ {a ℓ₁ ℓ₂} → Poset a ℓ₁ ℓ₂ → Poset _ _ _
≤-partialOrder po = record
  { isPartialOrder = ≤-isPartialOrder isPartialOrder
  } where open Poset po

≤-decTotalOrder : ∀ {a ℓ₁ ℓ₂} → DecTotalOrder a ℓ₁ ℓ₂ →
                  DecTotalOrder _ _ _
≤-decTotalOrder dtot = record
  { isDecTotalOrder = ≤-isDecTotalOrder isDecTotalOrder
  } where open DecTotalOrder dtot
