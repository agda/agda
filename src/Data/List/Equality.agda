------------------------------------------------------------------------
-- List equality
------------------------------------------------------------------------

module Data.List.Equality where

open import Data.List
open import Relation.Nullary
open import Relation.Binary

module Equality (S : Setoid) where

  open Setoid S renaming (_≈_ to _≊_)

  infixr 5 _∷_
  infix  4 _≈_

  data _≈_ : List carrier → List carrier → Set where
    []  : [] ≈ []
    _∷_ : ∀ {x xs y ys} (x≈y : x ≊ y) (xs≈ys : xs ≈ ys) →
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
    refl' {[]}     = []
    refl' {x ∷ xs} = refl ∷ refl' {xs}

    sym' : Symmetric _≈_
    sym' []            = []
    sym' (x≈y ∷ xs≈ys) = sym x≈y ∷ sym' xs≈ys

    trans' : Transitive _≈_
    trans' []            []            = []
    trans' (x≈y ∷ xs≈ys) (y≈z ∷ ys≈zs) =
      trans x≈y y≈z ∷ trans' xs≈ys ys≈zs

  open Setoid setoid public hiding (_≈_)

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
    dec []       []       = yes []
    dec (x ∷ xs) (y ∷ ys) with x ≟ y | dec xs ys
    ... | yes x≈y | yes xs≈ys = yes (x≈y ∷ xs≈ys)
    ... | no ¬x≈y | _         = no helper
      where
      helper : ¬ _≈_ (x ∷ xs) (y ∷ ys)
      helper (x≈y ∷ _) = ¬x≈y x≈y
    ... | _       | no ¬xs≈ys = no helper
      where
      helper : ¬ _≈_ (x ∷ xs) (y ∷ ys)
      helper (_ ∷ xs≈ys) = ¬xs≈ys xs≈ys
    dec []       (y ∷ ys) = no λ()
    dec (x ∷ xs) []       = no λ()

  open DecSetoid decSetoid public

module PropositionalEquality {A : Set} where

  open import Relation.Binary.PropositionalEquality as PropEq
    using (_≡_) renaming (refl to ≡-refl)
  open Equality (PropEq.setoid A) public

  ≈⇒≡ : _≈_ ⇒ _≡_
  ≈⇒≡ []               = ≡-refl
  ≈⇒≡ (≡-refl ∷ xs≈ys) with ≈⇒≡ xs≈ys
  ≈⇒≡ (≡-refl ∷ xs≈ys) | ≡-refl = ≡-refl
