------------------------------------------------------------------------
-- Vectors defined in terms of Data.Star
------------------------------------------------------------------------

module Data.Star.Vec where

open import Data.Star
open import Data.Star.Nat
open import Data.Star.Fin
import Data.Star.Decoration as Dec
open Dec hiding (lookup)
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

-- Unfortunately we don't get append for free.

infixr 5 _++_

_++_ : forall {a m n} -> Vec a m -> Vec a n -> Vec a (m + n)
_++_ {a = a} {n = n} xs ys = gmap plus lift xs ◅▻ ys
  where
  plus = map-NonEmpty (\m -> m + n)

  lift : DecoratedWith (\_ -> a) =[ plus ]⇒ DecoratedWith (\_ -> a)
  lift (↦ x) = ↦ x

-- Safe lookup.

lookup : forall {a n} -> Fin n -> Vec a n -> a
lookup i xs with Dec.lookup i xs
... | result _ x = x
