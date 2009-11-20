------------------------------------------------------------------------
-- Lexicographic ordering of lists
------------------------------------------------------------------------

-- The definition of lexicographic ordering used here is suitable if
-- the argument order is a (non-strict) partial order. The
-- lexicographic ordering itself can be either strict or non-strict,
-- depending on the value of a parameter.

module Relation.Binary.List.NonStrictLex where

open import Data.Empty
open import Data.Function
open import Data.Unit using (⊤; tt)
open import Data.Product
open import Data.List
open import Relation.Nullary
open import Relation.Binary

import Relation.Binary.NonStrictToStrict as Conv
import Relation.Binary.List.StrictLex as Strict

open import Relation.Binary.List.Pointwise as Pointwise using ([])

private
 module Dummy {A : Set} where

  Lex : (P : Set) → (≈ ≤ : Rel A) → Rel (List A)
  Lex P ≈ ≤ = Strict.Lex P ≈ (Conv._<_ ≈ ≤)

  -- Strict lexicographic ordering.

  Lex-< : (≈ ≤ : Rel A) → Rel (List A)
  Lex-< = Lex ⊥

  -- Non-strict lexicographic ordering.

  Lex-≤ : (≈ ≤ : Rel A) → Rel (List A)
  Lex-≤ = Lex ⊤

  ------------------------------------------------------------------------
  -- Properties

  ≤-reflexive : ∀ ≈ ≤ → Pointwise.Rel ≈ ⇒ Lex-≤ ≈ ≤
  ≤-reflexive ≈ ≤ = Strict.≤-reflexive ≈ (Conv._<_ ≈ ≤)

  <-irreflexive : ∀ {≈ ≤} → Irreflexive (Pointwise.Rel ≈) (Lex-< ≈ ≤)
  <-irreflexive {≈} {≤} =
    Strict.<-irreflexive {< = Conv._<_ ≈ ≤} (Conv.irrefl ≈ ≤)

  transitive : ∀ {P ≈ ≤} →
               IsPartialOrder ≈ ≤ → Transitive (Lex P ≈ ≤)
  transitive po =
    Strict.transitive
       isEquivalence
       (Conv.<-resp-≈ _ _ isEquivalence ≤-resp-≈)
       (Conv.trans _ _ po)
    where open IsPartialOrder po

  antisymmetric : ∀ {P ≈ ≤} →
                  Symmetric ≈ → Antisymmetric ≈ ≤ →
                  Antisymmetric (Pointwise.Rel ≈) (Lex P ≈ ≤)
  antisymmetric {≈ = ≈} {≤} sym antisym =
    Strict.antisymmetric sym (Conv.irrefl ≈ ≤)
                         (Conv.antisym⟶asym ≈ _ antisym)

  <-asymmetric : ∀ {≈ ≤} →
                 IsEquivalence ≈ → ≤ Respects₂ ≈ →
                 Antisymmetric ≈ ≤ → Asymmetric (Lex-< ≈ ≤)
  <-asymmetric {≈} eq resp antisym  =
    Strict.<-asymmetric sym (Conv.<-resp-≈ _ _ eq resp)
                        (Conv.antisym⟶asym ≈ _ antisym)
    where open IsEquivalence eq

  respects₂ : ∀ {P ≈ ≤} →
              IsEquivalence ≈ → ≤ Respects₂ ≈ →
              Lex P ≈ ≤ Respects₂ Pointwise.Rel ≈
  respects₂ eq resp = Strict.respects₂ eq (Conv.<-resp-≈ _ _ eq resp)

  decidable : ∀ {P ≈ ≤} →
              Dec P → Decidable ≈ → Decidable ≤ →
              Decidable (Lex P ≈ ≤)
  decidable dec-P dec-≈ dec-≤ =
    Strict.decidable dec-P dec-≈ (Conv.decidable _ _ dec-≈ dec-≤)

  <-decidable : ∀ {≈ ≤} →
                Decidable ≈ → Decidable ≤ → Decidable (Lex-< ≈ ≤)
  <-decidable = decidable (no id)

  ≤-decidable : ∀ {≈ ≤} →
                Decidable ≈ → Decidable ≤ → Decidable (Lex-≤ ≈ ≤)
  ≤-decidable = decidable (yes tt)

  ≤-total : ∀ {≈ ≤} → Symmetric ≈ → Decidable ≈ →
            Antisymmetric ≈ ≤ → Total ≤ →
            Total (Lex-≤ ≈ ≤)
  ≤-total sym dec-≈ antisym tot =
    Strict.≤-total sym (Conv.trichotomous _ _ sym dec-≈ antisym tot)

  <-compare : ∀ {≈ ≤} → Symmetric ≈ → Decidable ≈ →
              Antisymmetric ≈ ≤ → Total ≤ →
              Trichotomous (Pointwise.Rel ≈) (Lex-< ≈ ≤)
  <-compare sym dec-≈ antisym tot =
    Strict.<-compare sym (Conv.trichotomous _ _ sym dec-≈ antisym tot)

  -- Some collections of properties which are preserved by Lex-≤ or
  -- Lex-<.

  ≤-isPreorder : ∀ {≈ ≤} →
                 IsPartialOrder ≈ ≤ →
                 IsPreorder (Pointwise.Rel ≈) (Lex-≤ ≈ ≤)
  ≤-isPreorder po =
    Strict.≤-isPreorder
       isEquivalence (Conv.trans _ _ po)
       (Conv.<-resp-≈ _ _ isEquivalence ≤-resp-≈)
   where open IsPartialOrder po

  ≤-isPartialOrder : ∀ {≈ ≤} →
                     IsPartialOrder ≈ ≤ →
                     IsPartialOrder (Pointwise.Rel ≈) (Lex-≤ ≈ ≤)
  ≤-isPartialOrder po =
    Strict.≤-isPartialOrder
      (Conv.isPartialOrder⟶isStrictPartialOrder _ _ po)

  ≤-isTotalOrder : ∀ {≈ ≤} →
                   Decidable ≈ → IsTotalOrder ≈ ≤ →
                   IsTotalOrder (Pointwise.Rel ≈) (Lex-≤ ≈ ≤)
  ≤-isTotalOrder dec tot =
    Strict.≤-isTotalOrder
      (Conv.isTotalOrder⟶isStrictTotalOrder _ _ dec tot)

  ≤-isDecTotalOrder : ∀ {≈ ≤} →
                      IsDecTotalOrder ≈ ≤ →
                      IsDecTotalOrder (Pointwise.Rel ≈) (Lex-≤ ≈ ≤)
  ≤-isDecTotalOrder dtot =
    Strict.≤-isDecTotalOrder
      (Conv.isDecTotalOrder⟶isStrictTotalOrder _ _ dtot)

  <-isStrictPartialOrder : ∀ {≈ ≤} →
    IsPartialOrder ≈ ≤ →
    IsStrictPartialOrder (Pointwise.Rel ≈) (Lex-< ≈ ≤)
  <-isStrictPartialOrder po =
    Strict.<-isStrictPartialOrder
      (Conv.isPartialOrder⟶isStrictPartialOrder _ _ po)

  <-isStrictTotalOrder : ∀ {≈ ≤} →
    Decidable ≈ → IsTotalOrder ≈ ≤ →
    IsStrictTotalOrder (Pointwise.Rel ≈) (Lex-< ≈ ≤)
  <-isStrictTotalOrder dec tot =
    Strict.<-isStrictTotalOrder
      (Conv.isTotalOrder⟶isStrictTotalOrder _ _ dec tot)

open Dummy public

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
