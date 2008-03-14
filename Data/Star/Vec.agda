------------------------------------------------------------------------
-- Vectors defined in terms of Data.Star
------------------------------------------------------------------------

module Data.Star.Vec where

open import Data.Star
open import Data.Star.Nat
open import Data.Star.Fin
open import Data.Star.Decoration
open import Data.Star.List using ([_])
open import Relation.Binary
open import Relation.Binary.Consequences
open import Data.Function
open import Data.Unit

-- The vector type. Vectors are natural numbers decorated with extra
-- information (i.e. elements).

Vec : Set -> ℕ -> Set
Vec a = All (\_ -> a)

-- Nil and cons.

[] : forall {a} -> Vec a zero
[] = ε

infixr 5 _∷_

_∷_ : forall {a n} -> a -> Vec a n -> Vec a (suc n)
x ∷ xs = ↦ x ◅ xs

-- Append.

infixr 5 _++_

_++_ : forall {a m n} -> Vec a m -> Vec a n -> Vec a (m + n)
_++_ = _◅◅◅_

-- Safe lookup.

Vec-lookup : forall {a n} -> Fin n -> Vec a n -> a
Vec-lookup i xs with lookup i xs
... | result _ x = x

------------------------------------------------------------------------
-- Conversions

fromList : forall {a} -> (xs : [ a ]) -> Vec a (length xs)
fromList ε        = []
fromList (x ◅ xs) = x ∷ fromList xs

toList : forall {a n} -> Vec a n -> [ a ]
toList = gmap (const tt) decoration
