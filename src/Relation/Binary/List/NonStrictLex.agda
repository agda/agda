------------------------------------------------------------------------
-- The Agda standard library
--
-- Lexicographic ordering of lists
------------------------------------------------------------------------

-- The definition of lexicographic ordering used here is suitable if
-- the argument order is a (non-strict) partial order. The
-- lexicographic ordering itself can be either strict or non-strict,
-- depending on the value of a parameter.

module Relation.Binary.List.NonStrictLex where

open import Data.Empty
open import Function
open import Data.Unit.Minimal using (⊤; tt)
open import Data.Product
open import Data.List
open import Level
open import Relation.Nullary
open import Relation.Binary

import Relation.Binary.NonStrictToStrict as Conv
import Relation.Binary.List.StrictLex as Strict

open import Relation.Binary.List.Pointwise as Pointwise using ([])

module _ {A : Set} where

  Lex : (P : Set) → (_≈_ _≤_ : Rel A zero) → Rel (List A) zero
  Lex P _≈_ _≤_ = Strict.Lex P _≈_ (Conv._<_ _≈_ _≤_)

  -- Strict lexicographic ordering.

  Lex-< : (_≈_ _≤_ : Rel A zero) → Rel (List A) zero
  Lex-< = Lex ⊥

  -- Non-strict lexicographic ordering.

  Lex-≤ : (_≈_ _≤_ : Rel A zero) → Rel (List A) zero
  Lex-≤ = Lex ⊤

  ------------------------------------------------------------------------
  -- Properties

  ≤-reflexive : ∀ _≈_ _≤_ → Pointwise.Rel _≈_ ⇒ Lex-≤ _≈_ _≤_
  ≤-reflexive _≈_ _≤_ = Strict.≤-reflexive _≈_ (Conv._<_ _≈_ _≤_)

  <-irreflexive : ∀ {_≈_ _≤_} →
                  Irreflexive (Pointwise.Rel _≈_) (Lex-< _≈_ _≤_)
  <-irreflexive {_≈_} {_≤_} =
    Strict.<-irreflexive {_<_ = Conv._<_ _≈_ _≤_} (Conv.irrefl _≈_ _≤_)

  transitive : ∀ {P _≈_ _≤_} →
               IsPartialOrder _≈_ _≤_ → Transitive (Lex P _≈_ _≤_)
  transitive po =
    Strict.transitive
       isEquivalence
       (Conv.<-resp-≈ _ _ isEquivalence ≤-resp-≈)
       (Conv.trans _ _ po)
    where open IsPartialOrder po

  antisymmetric : ∀ {P _≈_ _≤_} →
                  Symmetric _≈_ → Antisymmetric _≈_ _≤_ →
                  Antisymmetric (Pointwise.Rel _≈_) (Lex P _≈_ _≤_)
  antisymmetric {_≈_ = _≈_} {_≤_} sym antisym =
    Strict.antisymmetric sym (Conv.irrefl _≈_ _≤_)
                         (Conv.antisym⟶asym _≈_ _ antisym)

  <-asymmetric : ∀ {_≈_ _≤_} →
                 IsEquivalence _≈_ → _≤_ Respects₂ _≈_ →
                 Antisymmetric _≈_ _≤_ → Asymmetric (Lex-< _≈_ _≤_)
  <-asymmetric {_≈_} eq resp antisym  =
    Strict.<-asymmetric sym (Conv.<-resp-≈ _ _ eq resp)
                        (Conv.antisym⟶asym _≈_ _ antisym)
    where open IsEquivalence eq

  respects₂ : ∀ {P _≈_ _≤_} →
              IsEquivalence _≈_ → _≤_ Respects₂ _≈_ →
              Lex P _≈_ _≤_ Respects₂ Pointwise.Rel _≈_
  respects₂ eq resp = Strict.respects₂ eq (Conv.<-resp-≈ _ _ eq resp)

  decidable : ∀ {P _≈_ _≤_} →
              Dec P → Decidable _≈_ → Decidable _≤_ →
              Decidable (Lex P _≈_ _≤_)
  decidable dec-P dec-≈ dec-≤ =
    Strict.decidable dec-P dec-≈ (Conv.decidable _ _ dec-≈ dec-≤)

  <-decidable :
    ∀ {_≈_ _≤_} →
    Decidable _≈_ → Decidable _≤_ → Decidable (Lex-< _≈_ _≤_)
  <-decidable = decidable (no id)

  ≤-decidable :
    ∀ {_≈_ _≤_} →
    Decidable _≈_ → Decidable _≤_ → Decidable (Lex-≤ _≈_ _≤_)
  ≤-decidable = decidable (yes tt)

  ≤-total : ∀ {_≈_ _≤_} → Symmetric _≈_ → Decidable _≈_ →
            Antisymmetric _≈_ _≤_ → Total _≤_ →
            Total (Lex-≤ _≈_ _≤_)
  ≤-total sym dec-≈ antisym tot =
    Strict.≤-total sym (Conv.trichotomous _ _ sym dec-≈ antisym tot)

  <-compare : ∀ {_≈_ _≤_} → Symmetric _≈_ → Decidable _≈_ →
              Antisymmetric _≈_ _≤_ → Total _≤_ →
              Trichotomous (Pointwise.Rel _≈_) (Lex-< _≈_ _≤_)
  <-compare sym dec-≈ antisym tot =
    Strict.<-compare sym (Conv.trichotomous _ _ sym dec-≈ antisym tot)

  -- Some collections of properties which are preserved by Lex-≤ or
  -- Lex-<.

  ≤-isPreorder : ∀ {_≈_ _≤_} →
                 IsPartialOrder _≈_ _≤_ →
                 IsPreorder (Pointwise.Rel _≈_) (Lex-≤ _≈_ _≤_)
  ≤-isPreorder po =
    Strict.≤-isPreorder
       isEquivalence (Conv.trans _ _ po)
       (Conv.<-resp-≈ _ _ isEquivalence ≤-resp-≈)
   where open IsPartialOrder po

  ≤-isPartialOrder : ∀ {_≈_ _≤_} →
                     IsPartialOrder _≈_ _≤_ →
                     IsPartialOrder (Pointwise.Rel _≈_) (Lex-≤ _≈_ _≤_)
  ≤-isPartialOrder po =
    Strict.≤-isPartialOrder
      (Conv.isPartialOrder⟶isStrictPartialOrder _ _ po)

  ≤-isTotalOrder : ∀ {_≈_ _≤_} →
                   Decidable _≈_ → IsTotalOrder _≈_ _≤_ →
                   IsTotalOrder (Pointwise.Rel _≈_) (Lex-≤ _≈_ _≤_)
  ≤-isTotalOrder dec tot =
    Strict.≤-isTotalOrder
      (Conv.isTotalOrder⟶isStrictTotalOrder _ _ dec tot)

  ≤-isDecTotalOrder :
    ∀ {_≈_ _≤_} →
    IsDecTotalOrder _≈_ _≤_ →
    IsDecTotalOrder (Pointwise.Rel _≈_) (Lex-≤ _≈_ _≤_)
  ≤-isDecTotalOrder dtot =
    Strict.≤-isDecTotalOrder
      (Conv.isDecTotalOrder⟶isStrictTotalOrder _ _ dtot)

  <-isStrictPartialOrder : ∀ {_≈_ _≤_} →
    IsPartialOrder _≈_ _≤_ →
    IsStrictPartialOrder (Pointwise.Rel _≈_) (Lex-< _≈_ _≤_)
  <-isStrictPartialOrder po =
    Strict.<-isStrictPartialOrder
      (Conv.isPartialOrder⟶isStrictPartialOrder _ _ po)

  <-isStrictTotalOrder : ∀ {_≈_ _≤_} →
    Decidable _≈_ → IsTotalOrder _≈_ _≤_ →
    IsStrictTotalOrder (Pointwise.Rel _≈_) (Lex-< _≈_ _≤_)
  <-isStrictTotalOrder dec tot =
    Strict.<-isStrictTotalOrder
      (Conv.isTotalOrder⟶isStrictTotalOrder _ _ dec tot)

-- "Packages" (e.g. preorders) can also be handled.

≤-preorder : Poset _ _ _ → Preorder _ _ _
≤-preorder po = record
  { isPreorder = ≤-isPreorder isPartialOrder
  } where open Poset po

≤-partialOrder : Poset _ _ _ → Poset _ _ _
≤-partialOrder po = record
  { isPartialOrder = ≤-isPartialOrder isPartialOrder
  } where open Poset po

≤-decTotalOrder : DecTotalOrder _ _ _ → DecTotalOrder _ _ _
≤-decTotalOrder dtot = record
  { isDecTotalOrder = ≤-isDecTotalOrder isDecTotalOrder
  } where open DecTotalOrder dtot

<-strictPartialOrder : Poset _ _ _ → StrictPartialOrder _ _ _
<-strictPartialOrder po = record
  { isStrictPartialOrder = <-isStrictPartialOrder isPartialOrder
  } where open Poset po

<-strictTotalOrder : DecTotalOrder _ _ _ → StrictTotalOrder _ _ _
<-strictTotalOrder dtot = record
  { isStrictTotalOrder = <-isStrictTotalOrder _≟_ isTotalOrder
  } where open IsDecTotalOrder (DecTotalOrder.isDecTotalOrder dtot)
