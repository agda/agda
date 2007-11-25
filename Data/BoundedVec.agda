------------------------------------------------------------------------
-- Bounded vectors
------------------------------------------------------------------------

-- Vectors of a specified maximum length.

module Data.BoundedVec where

open import Data.Nat
import Data.List as List
open List using ([_])
import Data.Vec as Vec
open Vec using (Vec)
open import Relation.Binary.PropositionalEquality
open import Data.Nat.Properties
open ℕ-semiringSolver
open import Data.Fin
open import Logic

------------------------------------------------------------------------
-- The type

abstract

  data BoundedVec (a : Set) : ℕ -> Set where
    bVec : forall {m n} -> Vec a n -> BoundedVec a (n + m)

  [] : forall {a n} -> BoundedVec a n
  [] = bVec Vec.[]

  infixr 5 _∷_

  _∷_ : forall {a n} -> a -> BoundedVec a n -> BoundedVec a (suc n)
  x ∷ bVec xs = bVec (Vec._∷_ x xs)

------------------------------------------------------------------------
-- Pattern matching

infixr 5 _∷v_

data View (a : Set) : ℕ -> Set where
  []v  : forall {n} -> View a n
  _∷v_ : forall {n} -> a -> BoundedVec a n -> View a (suc n)

abstract

  view : forall {a n} -> BoundedVec a n -> View a n
  view (bVec Vec.[])         = []v
  view (bVec (Vec._∷_ x xs)) = x ∷v bVec xs

------------------------------------------------------------------------
-- Increasing the bound

abstract

  ↑ : forall {a n} -> BoundedVec a n -> BoundedVec a (suc n)
  ↑ {a = a} (bVec {m = m} {n = n} xs) =
    ≡-subst (BoundedVec a) lemma
            (bVec {m = suc m} xs)
    where
    M = var fz; N = var (fs fz)
    lemma = prove (Vec._∷_ m (Vec._∷_ n Vec.[]))
                  (N :+ (con 1 :+ M))
                  (con 1 :+ (N :+ M))
                  ≡-refl

------------------------------------------------------------------------
-- Conversions

abstract

  fromList : forall {a} -> (xs : [ a ]) -> BoundedVec a (List.length xs)
  fromList {a = a} xs =
    ≡-subst (BoundedVec a) lemma
            (bVec {m = zero} (Vec.fromList xs))
    where
    M = var fz
    lemma = prove (Vec._∷_ (List.length xs) Vec.[]) (M :+ con 0) M ≡-refl

  toList : forall {a n} -> BoundedVec a n -> [ a ]
  toList (bVec xs) = Vec.toList xs
