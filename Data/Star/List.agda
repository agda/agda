------------------------------------------------------------------------
-- Lists defined in terms of Data.Star
------------------------------------------------------------------------

module Data.Star.List where

open import Data.Star
open import Data.Unit
open import Relation.Binary.Simple
open import Data.Star.Nat

-- Lists.

[_] : Set -> Set
[ a ] = Star (Const a) tt tt

-- Nil and cons.

[] : forall {a} -> [ a ]
[] = ε

infixr 5 _∷_

_∷_ : forall {a} -> a -> [ a ] -> [ a ]
_∷_ = _◅_

-- The sum of the elements in a list containing natural numbers.

sum : [ ℕ ] -> ℕ
sum = fold (Star Always) _+_ zero
