------------------------------------------------------------------------
-- Bounded vectors (inefficient implementation)
------------------------------------------------------------------------

-- Vectors of a specified maximum length.

module Data.Star.BoundedVec where

open import Data.Star
open import Data.Star.Nat
open import Data.Star.Fin
open import Data.Star.Decoration
open import Data.Star.List using ([_])
open import Data.Unit
open import Data.Function
open import Data.Maybe
open import Relation.Binary
open import Relation.Binary.Consequences
open import Category.Monad

------------------------------------------------------------------------
-- The type

-- Finite sets decorated with elements (note the use of suc).

BoundedVec : Set -> ℕ -> Set
BoundedVec a n = Any (\_ -> a) (\_ -> ⊤) (suc n)

[] : forall {a n} -> BoundedVec a n
[] = this tt

infixr 5 _∷_

_∷_ : forall {a n} -> a -> BoundedVec a n -> BoundedVec a (suc n)
_∷_ = that

------------------------------------------------------------------------
-- Increasing the bound

-- Note that this operation is linear in the length of the list.

↑ : forall {a n} -> BoundedVec a n -> BoundedVec a (suc n)
↑ {a} = gmap inc lift
  where
  open RawMonad MaybeMonad

  inc = _<$>_ (map-NonEmpty suc)

  lift : Pointer (\_ -> a) (\_ -> ⊤) =[ inc ]⇒
         Pointer (\_ -> a) (\_ -> ⊤)
  lift (step x) = step x
  lift (done _) = done _
