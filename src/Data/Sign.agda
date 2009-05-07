------------------------------------------------------------------------
-- Signs
------------------------------------------------------------------------

module Data.Sign where

open import Data.Function
open import Relation.Nullary
open import Relation.Binary
open import Relation.Binary.PropositionalEquality

-- Signs.

data Sign : Set where
  :- : Sign
  :0 : Sign
  :+ : Sign

-- Decidable equality.

_≟_ : Decidable {Sign} _≡_
:- ≟ :- = yes refl
:- ≟ :0 = no λ()
:- ≟ :+ = no λ()
:0 ≟ :- = no λ()
:0 ≟ :0 = yes refl
:0 ≟ :+ = no λ()
:+ ≟ :- = no λ()
:+ ≟ :0 = no λ()
:+ ≟ :+ = yes refl
