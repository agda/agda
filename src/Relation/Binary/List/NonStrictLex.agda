------------------------------------------------------------------------
-- Lexicographic ordering on lists.
------------------------------------------------------------------------

-- Lexicographic ordering on lists defined using a non-strict 
-- relation and an equivalence relation. The lexicographic ordering 
-- itself can be either strict or non-strict, depending on a parameter.

module Relation.Binary.List.NonStrictLex where

open import Data.Empty
open import Data.Unit using (⊤; tt)
open import Data.Product
open import Data.List
open import Relation.Nullary
open import Relation.Binary

import Relation.Binary.NonStrictToStrict as Conv
import Relation.Binary.List.StrictLex as Strict

open import Relation.Binary.List.Pointwise as Pointwise
   using ([]; _∷_; List-Rel; List-head; List-tail)

private 
 module Dummy {a : Set} where

  List-Lex : (P : Set) → (≈ ≤ : Rel a) → Rel (List a)
  List-Lex P ≈ ≤ = Strict.List-Lex P ≈ (Conv._<_ ≈ ≤)

  -- Strict Lexicographic ordering

  List-Lex-< : (≈ ≤ : Rel a) → Rel (List a)
  List-Lex-< = List-Lex ⊥

  -- Non-Strict Lexicographic ordering

  List-Lex-≤ : (≈ ≤ : Rel a) → Rel (List a)
  List-Lex-≤ = List-Lex ⊤

  ------------------------------------------------------------------------
  -- Properties

  List-≤-reflexive : ∀ ≈ ≤ → (List-Rel ≈) ⇒ (List-Lex-≤ ≈ ≤)
  List-≤-reflexive ≈ ≤ = Strict.List-≤-reflexive ≈ (Conv._<_ ≈ ≤)


  List-<-irreflexive : ∀ {≈ ≤} → Irreflexive (List-Rel ≈) (List-Lex-< ≈ ≤)
  List-<-irreflexive {≈} {≤} = 
    Strict.List-<-irreflexive {< = (Conv._<_ ≈ ≤)} (Conv.irrefl ≈ ≤)

  List-transitive : ∀ {P ≈ ≤} → IsPartialOrder ≈ ≤ →
                    Transitive (List-Lex P ≈ ≤)
  List-transitive {P} {≈} {≤} po  = 
    Strict.List-transitive {P = P}{≈}{Conv._<_ ≈ ≤}
       (IsPreorder.isEquivalence isPreorder) 
       (Conv.<-resp-≈ _ _ (IsPreorder.isEquivalence isPreorder) 
         (IsPreorder.∼-resp-≈ isPreorder)) 
       (Conv.trans _ _ po)
    where open IsPartialOrder po

  List-antisymmetric :
    ∀ {P ≈ ≤} → Symmetric ≈ → Antisymmetric ≈ ≤ →
    Antisymmetric (List-Rel ≈) (List-Lex P ≈ ≤)
  List-antisymmetric {P}{≈}{≤} sym antisym = 
    Strict.List-antisymmetric {P = P}{≈}{Conv._<_ ≈ ≤}
       sym (Conv.irrefl ≈ ≤) (Conv.antisym⟶asym ≈ _ antisym)

  List-<-asymmetric :
    ∀ {≈ ≤} → IsEquivalence ≈ → ≤ Respects₂ ≈ → 
      Antisymmetric ≈ ≤ → Asymmetric (List-Lex-< ≈ ≤)
  List-<-asymmetric {≈} {≤} eq resp antisym  =
    Strict.List-<-asymmetric (sym eq) (Conv.<-resp-≈ _ _ eq resp) 
      (Conv.antisym⟶asym ≈ _ antisym)
    where open IsEquivalence

  List-≈-respects₂ : 
    ∀ {P ≈ ≤} → IsEquivalence ≈ → ≤ Respects₂ ≈ →
    (List-Lex P ≈ ≤) Respects₂ (List-Rel ≈)
  List-≈-respects₂ eq resp = 
    Strict.List-≈-respects₂ eq (Conv.<-resp-≈ _ _ eq resp) 
         
  List-decidable : ∀ {P ≈ ≤} → Decidable ≈ → Decidable ≤ →
                   Dec ((List-Lex P ≈ ≤) [] []) →
                   Decidable (List-Lex P ≈ ≤)
  List-decidable dec-≈ dec-≤ []≟[] = 
    Strict.List-decidable dec-≈ (Conv.decidable _ _ dec-≈ dec-≤) []≟[]

  List-<-decidable :  ∀ {≈ ≤} → Decidable ≈ → Decidable ≤ →
                      Decidable (List-Lex-< ≈ ≤)
  List-<-decidable {≈} {<} dec-≈ dec-≤ = 
    List-decidable dec-≈ dec-≤ (no Strict.¬[]<[])

  List-≤-decidable :  ∀ {≈ ≤} → Decidable ≈ → Decidable ≤ →
                      Decidable (List-Lex-≤ ≈ ≤)
  List-≤-decidable {≈} {<} dec-≈ dec-≤ = 
    List-decidable dec-≈ dec-≤ (yes (Strict.base tt))

  List-≤-total : ∀ {≈ ≤} → Symmetric ≈ → Decidable ≈ → 
                   Antisymmetric ≈ ≤ → Total ≤ → 
                   Total (List-Lex-≤ ≈ ≤)
  List-≤-total sym dec-≈ antisym tot =
    Strict.List-≤-total sym (Conv.trichotomous _ _ sym dec-≈ antisym tot)

  List-<-compare : ∀ {≈ ≤} → Symmetric ≈ → Decidable ≈ → 
                   Antisymmetric ≈ ≤ → Total ≤ →
                   Trichotomous (List-Rel ≈) (List-Lex-< ≈ ≤)
  List-<-compare sym dec-≈ antisym tot =
    Strict.List-<-compare sym (Conv.trichotomous _ _ sym dec-≈ antisym tot)

  -- Some collections of properties which are preserved by List-Lex.
  
  List-≤-isPreorder : ∀ {≈ ≤} → IsPartialOrder ≈ ≤ →
                    IsPreorder (List-Rel ≈) (List-Lex-≤ ≈ ≤)
  List-≤-isPreorder po = 
    Strict.List-≤-isPreorder 
       isEquivalence (Conv.trans _ _ po) 
       (Conv.<-resp-≈ _ _ isEquivalence ∼-resp-≈)
   where pre = IsPartialOrder.isPreorder po
         open IsPreorder pre

  List-≤-isPartialOrder :
    ∀ {≈ ≤} → IsPartialOrder ≈ ≤ → 
    IsPartialOrder (List-Rel ≈) (List-Lex-≤ ≈ ≤)
  List-≤-isPartialOrder po = 
    Strict.List-≤-isPartialOrder (Conv.isPartialOrder⟶isStrictPartialOrder _ _ po)

  List-≤-isTotalOrder : 
    ∀ {≈ ≤} → Decidable ≈ → IsTotalOrder ≈ ≤ → 
    IsTotalOrder (List-Rel ≈) (List-Lex-≤ ≈ ≤)
  List-≤-isTotalOrder dec tot = 
    Strict.List-≤-isTotalOrder (Conv.isTotalOrder⟶isStrictTotalOrder _ _ dec tot)

  List-≤-isDecTotalOrder :
    ∀ {≈ ≤} → IsDecTotalOrder ≈ ≤ →
    IsDecTotalOrder (List-Rel ≈) (List-Lex-≤ ≈ ≤)
  List-≤-isDecTotalOrder dtot = 
    Strict.List-≤-isDecTotalOrder
      (Conv.isDecTotalOrder⟶isStrictTotalOrder _ _ dtot)

  List-<-isStrictPartialOrder : 
    ∀ {≈ ≤} → IsPartialOrder ≈ ≤ → 
    IsStrictPartialOrder (List-Rel ≈) (List-Lex-< ≈ ≤)
  List-<-isStrictPartialOrder po = 
    Strict.List-<-isStrictPartialOrder (Conv.isPartialOrder⟶isStrictPartialOrder _ _ po)

  List-<-isStrictTotalOrder :
    ∀ {≈ ≤} → Decidable ≈ → IsTotalOrder ≈ ≤ → 
    IsStrictTotalOrder (List-Rel ≈) (List-Lex-< ≈ ≤)
  List-<-isStrictTotalOrder dec tot = 
    Strict.List-<-isStrictTotalOrder (Conv.isTotalOrder⟶isStrictTotalOrder _ _ dec tot)

open Dummy public

-- "Packages" (e.g. preorders) can also be combined.

List-≤-preorder : Poset → Preorder
List-≤-preorder po = record
  { isPreorder = List-≤-isPreorder isPartialOrder
  }
  where open Poset po

List-≤-partialOrder : Poset → Poset
List-≤-partialOrder po = record
  { isPartialOrder = List-≤-isPartialOrder isPartialOrder
  }
  where open Poset po

List-<-strictPartialOrder : Poset → StrictPartialOrder
List-<-strictPartialOrder po = record
  { isStrictPartialOrder = List-<-isStrictPartialOrder isPartialOrder
  }
  where open Poset po

  -- List-≤-totalOrder and List-<-strictTotalOrder are a bit 
  -- stronger than necessary -- ≤ need not be decidable.

List-≤-totalOrder : DecTotalOrder → TotalOrder
List-≤-totalOrder dtot = record
  { isTotalOrder = List-≤-isTotalOrder _≟_ isTotalOrder
  }
  where open IsDecTotalOrder (DecTotalOrder.isDecTotalOrder dtot)

List-<-strictTotalOrder : DecTotalOrder → StrictTotalOrder
List-<-strictTotalOrder dtot = record
  { isStrictTotalOrder = List-<-isStrictTotalOrder _≟_ isTotalOrder
  }
  where open IsDecTotalOrder (DecTotalOrder.isDecTotalOrder dtot)

List-≤-decTotalOrder : DecTotalOrder → DecTotalOrder
List-≤-decTotalOrder dtot = record
  { isDecTotalOrder = List-≤-isDecTotalOrder isDecTotalOrder }
  where open DecTotalOrder dtot