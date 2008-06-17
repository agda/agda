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

private
  -≢0 : :- ≢ :0
  -≢0 ()

  -≢+ : :- ≢ :+
  -≢+ ()

  0≢+ : :0 ≢ :+
  0≢+ ()

_≟_ : Decidable {Sign} _≡_
:- ≟ :- = yes ≡-refl
:- ≟ :0 = no -≢0
:- ≟ :+ = no -≢+
:0 ≟ :- = no (-≢0 ∘ ≡-sym)
:0 ≟ :0 = yes ≡-refl
:0 ≟ :+ = no 0≢+
:+ ≟ :- = no (-≢+ ∘ ≡-sym )
:+ ≟ :0 = no (0≢+ ∘ ≡-sym )
:+ ≟ :+ = yes ≡-refl
