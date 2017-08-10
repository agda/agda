------------------------------------------------------------------------
-- The Agda standard library
--
-- Bounded vectors
------------------------------------------------------------------------

-- Vectors of a specified maximum length.

module Data.BoundedVec where

open import Data.Nat
open import Data.List.Base as List using (List)
open import Data.Vec as Vec using (Vec)
import Data.BoundedVec.Inefficient as Ineff
open import Relation.Binary.PropositionalEquality
open import Data.Nat.Properties
open SemiringSolver

------------------------------------------------------------------------
-- The type

abstract

  data BoundedVec {a} (A : Set a) : ℕ → Set a where
    bVec : ∀ {m n} (xs : Vec A n) → BoundedVec A (n + m)

  [] : ∀ {a n} {A : Set a} → BoundedVec A n
  [] = bVec Vec.[]

  infixr 5 _∷_

  _∷_ : ∀ {a n} {A : Set a} →
        A → BoundedVec A n → BoundedVec A (suc n)
  x ∷ bVec xs = bVec (Vec._∷_ x xs)

------------------------------------------------------------------------
-- Pattern matching

infixr 5 _∷v_

data View {a} (A : Set a) : ℕ → Set a where
  []v  : ∀ {n} → View A n
  _∷v_ : ∀ {n} (x : A) (xs : BoundedVec A n) → View A (suc n)

abstract

  view : ∀ {a n} {A : Set a} → BoundedVec A n → View A n
  view (bVec Vec.[])         = []v
  view (bVec (Vec._∷_ x xs)) = x ∷v bVec xs

------------------------------------------------------------------------
-- Increasing the bound

abstract

  ↑ : ∀ {a n} {A : Set a} → BoundedVec A n → BoundedVec A (suc n)
  ↑ {A = A} (bVec {m = m} {n = n} xs) =
    subst (BoundedVec A) lemma
            (bVec {m = suc m} xs)
    where
    lemma : n + (1 + m) ≡ 1 + (n + m)
    lemma = solve 2 (λ m n → n :+ (con 1 :+ m)  :=  con 1 :+ (n :+ m))
                    refl m n

------------------------------------------------------------------------
-- Conversions

module _ {a} {A : Set a} where

 abstract

  fromList : (xs : List A) → BoundedVec A (List.length xs)
  fromList xs =
    subst (BoundedVec A) lemma
            (bVec {m = zero} (Vec.fromList xs))
    where
    lemma : List.length xs + 0 ≡ List.length xs
    lemma = solve 1 (λ m → m :+ con 0  :=  m) refl _

  toList : ∀ {n} → BoundedVec A n → List A
  toList (bVec xs) = Vec.toList xs

  toInefficient : ∀ {n} → BoundedVec A n → Ineff.BoundedVec A n
  toInefficient xs with view xs
  ... | []v     = Ineff.[]
  ... | y ∷v ys = y Ineff.∷ toInefficient ys

  fromInefficient : ∀ {n} → Ineff.BoundedVec A n → BoundedVec A n
  fromInefficient Ineff.[]       = []
  fromInefficient (x Ineff.∷ xs) = x ∷ fromInefficient xs
