------------------------------------------------------------------------
-- List equality
------------------------------------------------------------------------

module Data.List.Equality where

open import Data.List
open import Relation.Nullary
open import Relation.Binary
open import Logic
open import Relation.Binary.PropositionalEquality

module Equality (S : Setoid) where

  open Setoid S

  data ListEq : [ carrier ] -> [ carrier ] -> Set where
    []-cong  : ListEq [] []
    _∷-cong_ : forall {x xs y ys} ->
               x ≈ y -> ListEq xs ys -> ListEq (x ∷ xs) (y ∷ ys)

  setoid : Setoid
  setoid = record
    { carrier = [ carrier ]
    ; _≈_     = ListEq
    ; isEquivalence = record
      { refl  = refl'
      ; sym   = sym'
      ; trans = trans'
      }
    }
    where
    refl' : Reflexive ListEq
    refl' {[]}     = []-cong
    refl' {x ∷ xs} = refl ∷-cong refl' {xs}

    sym' : Symmetric ListEq
    sym' []-cong = []-cong
    sym' (x≈y ∷-cong xs≈ys) = sym x≈y ∷-cong sym' xs≈ys

    trans' : Transitive ListEq
    trans' []-cong            []-cong            = []-cong
    trans' (x≈y ∷-cong xs≈ys) (y≈z ∷-cong ys≈zs) =
      trans x≈y y≈z ∷-cong trans' xs≈ys ys≈zs

module DecidableEquality (D : DecSetoid) where

  open DecSetoid D
  open Equality setoid renaming (setoid to List-setoid)

  decSetoid : DecSetoid
  decSetoid = record
    { carrier = [ carrier ]
    ; _≈_     = ListEq
    ; isDecEquivalence = record
      { isEquivalence = Setoid.isEquivalence List-setoid
      ; _≟_           = dec
      }
    }
    where
    dec : Decidable ListEq
    dec []       []       = yes []-cong
    dec (x ∷ xs) (y ∷ ys) with x ≟ y | dec xs ys
    ... | yes x≈y | yes xs≈ys = yes (x≈y ∷-cong xs≈ys)
    ... | no ¬x≈y | _         = no helper
      where
      helper : ¬ ListEq (x ∷ xs) (y ∷ ys)
      helper (x≈y ∷-cong _) = ¬x≈y x≈y
    ... | _       | no ¬xs≈ys = no helper
      where
      helper : ¬ ListEq (x ∷ xs) (y ∷ ys)
      helper (_ ∷-cong xs≈ys) = ¬xs≈ys xs≈ys
    dec []       (y ∷ ys) = no helper
      where
      helper : ¬ ListEq [] (y ∷ ys)
      helper ()
    dec (x ∷ xs) []       = no helper
      where
      helper : ¬ ListEq (x ∷ xs) []
      helper ()

module PropositionalEquality (a : Set) where

  open Equality (≡-setoid a)

  ListEq⇒≡ : ListEq ⇒ _≡_
  ListEq⇒≡ []-cong               = ≡-refl
  ListEq⇒≡ (≡-refl ∷-cong xs≈ys) with ListEq⇒≡ xs≈ys
  ListEq⇒≡ (≡-refl ∷-cong xs≈ys) | ≡-refl = ≡-refl
