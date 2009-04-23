------------------------------------------------------------------------
-- Bounded vectors
------------------------------------------------------------------------

-- Vectors of a specified maximum length.

module Data.BoundedVec where

open import Data.Nat
open import Data.List as List using (List)
open import Data.Vec as Vec using (Vec)
open import Relation.Binary.PropositionalEquality
open import Data.Nat.Properties
open SemiringSolver

------------------------------------------------------------------------
-- The type

abstract

  data BoundedVec (a : Set) : ℕ → Set where
    bVec : ∀ {m n} (xs : Vec a n) → BoundedVec a (n + m)

  [] : ∀ {a n} → BoundedVec a n
  [] = bVec Vec.[]

  infixr 5 _∷_

  _∷_ : ∀ {a n} → a → BoundedVec a n → BoundedVec a (suc n)
  x ∷ bVec xs = bVec (Vec._∷_ x xs)

------------------------------------------------------------------------
-- Pattern matching

infixr 5 _∷v_

data View (a : Set) : ℕ → Set where
  []v  : ∀ {n} → View a n
  _∷v_ : ∀ {n} (x : a) (xs : BoundedVec a n) → View a (suc n)

abstract

  view : ∀ {a n} → BoundedVec a n → View a n
  view (bVec Vec.[])         = []v
  view (bVec (Vec._∷_ x xs)) = x ∷v bVec xs

------------------------------------------------------------------------
-- Increasing the bound

abstract

  ↑ : ∀ {a n} → BoundedVec a n → BoundedVec a (suc n)
  ↑ {a = a} (bVec {m = m} {n = n} xs) =
    subst (BoundedVec a) lemma
            (bVec {m = suc m} xs)
    where
    lemma = solve 2 (λ m n → n :+ (con 1 :+ m)  :=  con 1 :+ (n :+ m))
                    refl m n

------------------------------------------------------------------------
-- Conversions

abstract

  fromList : ∀ {a} → (xs : List a) → BoundedVec a (List.length xs)
  fromList {a = a} xs =
    subst (BoundedVec a) lemma
            (bVec {m = zero} (Vec.fromList xs))
    where lemma = solve 1 (λ m → m :+ con 0  :=  m) refl _

  toList : ∀ {a n} → BoundedVec a n → List a
  toList (bVec xs) = Vec.toList xs
