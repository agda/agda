------------------------------------------------------------------------
-- List equality
------------------------------------------------------------------------

module Data.List.Equality where

open import Data.List
open import Relation.Nullary
open import Relation.Binary
open import Relation.Binary.List.Pointwise

module Equality (S : Setoid) where

  open import Relation.Binary.List.Pointwise public using ([]; _∷_)
  open Setoid S renaming (_≈_ to _≊_)

  infix  4 _≈_

  _≈_ : Rel (List carrier)
  _≈_ = List-Rel _≊_

  setoid : Setoid
  setoid = List-setoid S

  open Setoid setoid public hiding (_≈_)

module DecidableEquality (D : DecSetoid) where

  decSetoid : DecSetoid
  decSetoid = List-decSetoid D

  open DecSetoid decSetoid public

module PropositionalEquality {A : Set} where

  open import Relation.Binary.PropositionalEquality as PropEq
    using (_≡_) renaming (refl to ≡-refl)
  open Equality (PropEq.setoid A) public

  ≈⇒≡ : _≈_ ⇒ _≡_
  ≈⇒≡ []               = ≡-refl
  ≈⇒≡ (≡-refl ∷ xs≈ys) with ≈⇒≡ xs≈ys
  ≈⇒≡ (≡-refl ∷ xs≈ys) | ≡-refl = ≡-refl
