------------------------------------------------------------------------
-- Natural numbers
------------------------------------------------------------------------

-- For some reason Agda panics when DivMod.helper is checked for
-- pattern completeness.

{-# OPTIONS --no-coverage-check
  #-}

module Data.Nat where

open import Data.Function
open import Logic
open import Data.Sum
open import Data.Fin
open import Data.Product
open import Relation.Nullary
open import Relation.Binary
open import Relation.Binary.PropositionalEquality
open import Logic.Induction.Nat
open import Data.Nat.Properties.Core

infixl 7 _*_ _⊓_
infixl 6 _∸_ _⊔_

------------------------------------------------------------------------
-- The types

open import Data.Nat.Core public

------------------------------------------------------------------------
-- A generalisation of the arithmetic operations

fold : {a : Set} -> a -> (a -> a) -> ℕ -> a
fold z s zero    = z
fold z s (suc n) = s (fold z s n)

module GeneralisedArithmetic {a : Set} (0# : a) (1+ : a -> a) where

  add : ℕ -> a -> a
  add n z = fold z 1+ n

  mul : (+ : a -> a -> a) -> (ℕ -> a -> a)
  mul _+_ n x = fold 0# (\s -> s + x) n

------------------------------------------------------------------------
-- Arithmetic

-- pred and _+_ are defined in Data.Nat.Core.

_∸_ : ℕ -> ℕ -> ℕ
m     ∸ zero  = m
zero  ∸ suc n = zero
suc m ∸ suc n = m ∸ n

{-# BUILTIN NATMINUS _∸_ #-}

_*_ : ℕ -> ℕ -> ℕ
zero  * n = zero
suc m * n = m * n + n

{-# BUILTIN NATTIMES _*_ #-}

-- Max.

_⊔_ : ℕ -> ℕ -> ℕ
zero  ⊔ n     = n
suc m ⊔ zero  = suc m
suc m ⊔ suc n = suc (m ⊔ n)

-- Min.

_⊓_ : ℕ -> ℕ -> ℕ
zero  ⊓ n     = zero
suc m ⊓ zero  = zero
suc m ⊓ suc n = suc (m ⊓ n)

------------------------------------------------------------------------
-- Queries

-- ℕ-total, zero≢suc, _ℕ-≟_, suc≰zero, ≤-pred and _≤?_ are defined in
-- Data.Nat.Core.

-- A comparison view. Taken from "View from the left"
-- (McBride/McKinna); details may differ.

data Ordering : ℕ -> ℕ -> Set where
  less    : forall m k -> Ordering m (suc (m + k))
  equal   : forall m   -> Ordering m m
  greater : forall m k -> Ordering (suc (m + k)) m

compare : forall m n -> Ordering m n
compare zero    zero    = equal   zero
compare (suc m) zero    = greater zero m
compare zero    (suc n) = less    zero n
compare (suc m) (suc n) with compare m n
compare (suc .m)           (suc .(suc m + k)) | less    m k = less    (suc m) k
compare (suc .m)           (suc .m)           | equal   m   = equal   (suc m)
compare (suc .(suc m + k)) (suc .m)           | greater m k = greater (suc m) k

------------------------------------------------------------------------
-- More arithmetic

-- Integer division.

module DivMod where
  Pred : ℕ -> Set
  Pred divisor = (dividend : ℕ) {≢0 : False (dividend ℕ-≟ 0)} ->
                 ℕ × Fin dividend

  helper : forall m n {o} ->
           Ordering m o -> o ≡ suc n -> <-Rec Pred m -> ℕ × Fin (suc n)
  helper .m                   .(m + k) (less m k)          ≡-refl rec = (0 , inject k (fromℕ m))
  helper .(suc n)             .n       (equal (suc n))     ≡-refl rec = (1 , fz)
  helper .(suc (suc (n + k))) .n       (greater (suc n) k) ≡-refl rec
    with rec (suc k) (s≤s (s≤s (n≤m+n n k))) (suc n)
  ... | (x , r) = (suc x , r)
  helper ._ _ (equal zero)     () _
  helper ._ _ (greater zero _) () _

  divMod : (divisor : ℕ) -> <-Rec Pred divisor -> Pred divisor
  divMod m rec zero    {≢0 = ()}
  divMod m rec (suc n) = helper m n (compare m (suc n)) ≡-refl rec

_divMod_ : (divisor dividend : ℕ) {≢0 : False (dividend ℕ-≟ 0)} ->
           ℕ × Fin dividend
_divMod_ = <-rec DivMod.Pred DivMod.divMod

------------------------------------------------------------------------
-- Some properties

ℕ-preorder : Preorder
ℕ-preorder = ≡-preorder ℕ

ℕ-setoid : Setoid
ℕ-setoid = ≡-setoid ℕ

ℕ-decSetoid : DecSetoid
ℕ-decSetoid = DecTotalOrder.Eq.decSetoid ℕ-decTotalOrder

-- ℕ-decTotalOrder, ℕ-poset and ≤-Reasoning are defined in
-- Data.Nat.Core.
