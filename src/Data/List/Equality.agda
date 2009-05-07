------------------------------------------------------------------------
-- List equality
------------------------------------------------------------------------

module Data.List.Equality where

open import Data.List
open import Relation.Nullary
open import Relation.Binary

module Equality (S : Setoid) where

  open Setoid S renaming (_≈_ to _≊_)

  infix 4 _≈_

  data _≈_ : List carrier → List carrier → Set where
    []-cong  : [] ≈ []
    _∷-cong_ : ∀ {x xs y ys} (x≈y : x ≊ y) (xs≈ys : xs ≈ ys) →
               x ∷ xs ≈ y ∷ ys

  setoid : Setoid
  setoid = record
    { carrier = List carrier
    ; _≈_     = _≈_
    ; isEquivalence = record
      { refl  = refl'
      ; sym   = sym'
      ; trans = trans'
      }
    }
    where
    refl' : Reflexive _≈_
    refl' {[]}     = []-cong
    refl' {x ∷ xs} = refl ∷-cong refl' {xs}

    sym' : Symmetric _≈_
    sym' []-cong = []-cong
    sym' (x≈y ∷-cong xs≈ys) = sym x≈y ∷-cong sym' xs≈ys

    trans' : Transitive _≈_
    trans' []-cong            []-cong            = []-cong
    trans' (x≈y ∷-cong xs≈ys) (y≈z ∷-cong ys≈zs) =
      trans x≈y y≈z ∷-cong trans' xs≈ys ys≈zs

module DecidableEquality (D : DecSetoid) where

  open DecSetoid D hiding (_≈_)
  open Equality setoid renaming (setoid to List-setoid)

  decSetoid : DecSetoid
  decSetoid = record
    { isDecEquivalence = record
      { isEquivalence = Setoid.isEquivalence List-setoid
      ; _≟_           = dec
      }
    }
    where
    dec : Decidable _≈_
    dec []       []       = yes []-cong
    dec (x ∷ xs) (y ∷ ys) with x ≟ y | dec xs ys
    ... | yes x≈y | yes xs≈ys = yes (x≈y ∷-cong xs≈ys)
    ... | no ¬x≈y | _         = no helper
      where
      helper : ¬ _≈_ (x ∷ xs) (y ∷ ys)
      helper (x≈y ∷-cong _) = ¬x≈y x≈y
    ... | _       | no ¬xs≈ys = no helper
      where
      helper : ¬ _≈_ (x ∷ xs) (y ∷ ys)
      helper (_ ∷-cong xs≈ys) = ¬xs≈ys xs≈ys
    dec []       (y ∷ ys) = no λ()
    dec (x ∷ xs) []       = no λ()

module PropositionalEquality (a : Set) where

  open import Relation.Binary.PropositionalEquality
  open Equality (setoid a)

  ≈⇒≡ : _≈_ ⇒ _≡_
  ≈⇒≡ []-cong             = refl
  ≈⇒≡ (refl ∷-cong xs≈ys) with ≈⇒≡ xs≈ys
  ≈⇒≡ (refl ∷-cong xs≈ys) | refl = refl
