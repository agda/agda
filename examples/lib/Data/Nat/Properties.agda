
module Data.Nat.Properties where

import Prelude
import Logic.Base
import Logic.Relations
import Logic.Equivalence
import Logic.Operations as Operations
import Logic.Identity
import Logic.ChainReasoning
import Data.Nat
import Data.Bool

open Prelude
open Data.Nat
open Logic.Base
open Logic.Relations
open Logic.Identity
open Data.Bool

module Proofs where

  module Ops = Operations.MonoEq Equiv
  open Ops

  module Chain = Logic.ChainReasoning.Poly.Homogenous _≡_ (\x -> refl) (\x y z -> trans)
  open Chain

  +zero : (n : Nat) -> n + zero ≡ n
  +zero  zero   = refl
  +zero (suc n) = cong suc (+zero n)

  +suc : (n m : Nat) -> n + suc m ≡ suc (n + m)
  +suc  zero   m = refl
  +suc (suc n) m = cong suc (+suc n m)

  +commute : Commutative _+_
  +commute x  zero   = +zero x
  +commute x (suc y) = trans (+suc x y) (cong suc (+commute x y))

  +assoc : Associative _+_
  +assoc  zero   y z = refl
  +assoc (suc x) y z = cong suc (+assoc x y z)

  *zero : (n : Nat) -> n * zero ≡ zero
  *zero  zero   = refl
  *zero (suc n) = *zero n

  *suc : (x y : Nat) -> x * suc y ≡ x + x * y
  *suc  zero   y = refl
  *suc (suc x) y =
    chain> suc x * suc y
       === suc (y + x * suc y)   by refl
       === suc (x + (y + x * y)) by cong suc
        ( chain> y + x * suc y
             === y + (x + x * y)  by cong (_+_ y) (*suc x y)
             === (y + x) + x * y  by +assoc y x (x * y)
             === (x + y) + x * y  by cong (flip _+_ (x * y)) (+commute y x)
             === x + (y + x * y)  by sym (+assoc x y (x * y))
        )
       === suc x + suc x * y     by refl

  *commute : (x y : Nat) -> x * y ≡ y * x
  *commute x  zero   = *zero x
  *commute x (suc y) = trans (*suc x y) (cong (_+_ x) (*commute x y))

  one* : (x : Nat) -> 1 * x ≡ x
  one* x = +zero x

  *one : (x : Nat) -> x * 1 ≡ x
  *one x = trans (*commute x 1) (one* x)

  *distrOver+L : (x y z : Nat) -> x * (y + z) ≡ x * y + x * z
  *distrOver+L  zero   y z = refl
  *distrOver+L (suc x) y z =
    chain> suc x * (y + z)
       === (y + z) + x * (y + z)      by refl
       === (y + z) + (x * y + x * z)  by cong (_+_ (y + z)) ih
       === ((y + z) + x * y) + x * z  by +assoc (y + z) (x * y) (x * z)
       === (y + (z + x * y)) + x * z  by cong (flip _+_ (x * z)) (sym (+assoc y z (x * y)))
       === (y + (x * y + z)) + x * z  by cong (\w -> (y + w) + x * z) (+commute z (x * y))
       === ((y + x * y) + z) + x * z  by cong (flip _+_ (x * z)) (+assoc y (x * y) z)
       === (y + x * y) + (z + x * z)  by sym (+assoc (y + x * y) z (x * z))
       === suc x * y + suc x * z      by refl
    where
      ih = *distrOver+L x y z

  *distrOver+R : (x y z : Nat) -> (x + y) * z ≡ x * z + y * z
  *distrOver+R  zero   y z = refl
  *distrOver+R (suc x) y z =
    chain> (suc x + y) * z
       === z + (x + y) * z      by refl
       === z + (x * z + y * z)  by cong (_+_ z) (*distrOver+R x y z)
       === (z + x * z) + y * z  by +assoc z (x * z) (y * z)
       === suc x * z + y * z    by refl

  *assoc : Associative _*_
  *assoc  zero   y z = refl
  *assoc (suc x) y z =
    chain> suc x * (y * z)
       === y * z + x * (y * z)  by refl
       === y * z + (x * y) * z  by cong (_+_ (y * z)) ih
       === (y + x * y) * z      by sym (*distrOver+R y (x * y) z)
       === (suc x * y) * z      by refl
    where
      ih = *assoc x y z

  ≤refl : (n : Nat) -> IsTrue (n ≤ n)
  ≤refl  zero   = tt
  ≤refl (suc n) = ≤refl n

  <implies≤ : (n m : Nat) -> IsTrue (n < m) -> IsTrue (n ≤ m)
  <implies≤  zero    m      h = tt
  <implies≤ (suc n)  zero   ()
  <implies≤ (suc n) (suc m) h = <implies≤ n m h

  n-m≤n : (n m : Nat) -> IsTrue (n - m ≤ n)
  n-m≤n  zero    m      = tt
  n-m≤n (suc n)  zero   = ≤refl n
  n-m≤n (suc n) (suc m) = <implies≤ (n - m) (suc n) (n-m≤n n m)

--   mod≤ : (n m : Nat) -> IsTrue (mod n (suc m) ≤ m)
--   mod≤  zero   m = tt
--   mod≤ (suc n) m = mod≤ (n - m) m

open Proofs public

