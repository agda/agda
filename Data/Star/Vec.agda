------------------------------------------------------------------------
-- Vectors defined in terms of Data.Star
------------------------------------------------------------------------

-- Vectors don't fit very well into this framework.

module Data.Star.Vec where

open import Data.Star
open import Data.Star.Nat
open import Data.Star.Fin
open import Data.Star.Lookup
open import Relation.Binary
open import Data.Function

-- The vector relation and type.

data VecRel (a : Set) : Rel ℕ where
  ↦ : forall {n} -> a -> VecRel a (suc n) n

Vec : Set -> ℕ -> Set
Vec a n = Star (VecRel a) n zero

-- Nil and cons.

[] : forall {a} -> Vec a zero
[] = ε

infixr 5 _∷_

_∷_ : forall {a n} -> a -> Vec a n -> Vec a (suc n)
x ∷ xs = ↦ x ◅ xs

-- Unfortunately we don't get append for free.

infixr 5 _++_

_++_ : forall {a m n} -> Vec a m -> Vec a n -> Vec a (m + n)
_++_ {a = a} {n = n} xs ys = gmap (\i -> i + n) lift xs ◅▻ ys
  where
  lift : forall {i j} -> VecRel a i j -> VecRel a (i + n) (j + n)
  lift (↦ x) = ↦ x

-- Safe lookup. We have to fight for this one as well.

makePrefix : forall {a n} ->
             Fin n -> (xs : Vec a n) -> NonEmptyPrefixOf xs
makePrefix (done ◅ ε) (x   ◅ xs) = this
makePrefix (step ◅ i) (↦ x ◅ xs) = that (makePrefix i xs)
makePrefix (done ◅ (() ◅ _)) _

Vec-lookup : forall {a n} -> Fin n -> Vec a n -> a
Vec-lookup i xs with lookup xs (makePrefix i xs)
... | nonEmpty (↦ x) = x
