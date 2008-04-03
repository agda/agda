
module DivMod where

-- From examples/simple-lib
open import Lib.Vec
open import Lib.Nat
open import Lib.Id
open import Lib.Logic
open import Lib.Fin

-- Certified implementation of division and modulo
module Direct where

  data DivMod : Nat -> Nat -> Set where
    dm : forall {b} q (r : Fin b) -> DivMod (toNat r + q * b) b

  getQ : forall {a b} -> DivMod a b -> Nat
  getQ (dm q _) = q

  getR : forall {a b} -> DivMod a b -> Nat
  getR (dm _ r) = toNat r

  divModˢ : (a b : Nat) -> DivMod a (suc b)
  divModˢ zero    b = dm 0 zero
  divModˢ (suc a) b with divModˢ a b
  divModˢ (suc ._) b | dm q r with maxView r 
  divModˢ (suc ._) b | dm q .(fromNat b) | theMax
    with toNat (fromNat b) | lem-toNat-fromNat b
  ...  | .b | refl = dm {suc b} (suc q) zero
  divModˢ (suc ._) b | dm q .(weaken i)  | notMax i
    with toNat (weaken i) | lem-toNat-weaken i
  ...  | .(toNat i) | refl = dm q (suc i) 

  divMod : (a b : Nat){nz : NonZero b} -> DivMod a b
  divMod a zero {}
  divMod a (suc b) = divModˢ a b

-- Let's try the inductive version. Less obvious that this one is correct.
module Inductive where

  data DivMod : Nat -> Nat -> Set where
    dmZ : forall {b} (i : Fin b) -> DivMod (toNat i) b
    dmS : forall {a b} -> DivMod a b -> DivMod (b + a) b

  getQ : forall {a b} -> DivMod a b -> Nat
  getQ (dmZ _) = 0
  getQ (dmS d) = suc (getQ d)

  getR : forall {a b} -> DivMod a b -> Nat
  getR (dmZ r) = toNat r
  getR (dmS d) = getR d

  data BoundView (n : Nat) : Nat -> Set where
    below : (i : Fin n) -> BoundView n (toNat i)
    above : forall a    -> BoundView n (n + a)

  boundView : (a b : Nat) -> BoundView a b
  boundView zero b = above b
  boundView (suc a) zero    = below zero
  boundView (suc a) (suc b) with boundView a b
  boundView (suc a) (suc .(toNat i)) | below i = below (suc i)
  boundView (suc a) (suc .(a + k))   | above k = above k

  data _≤_ : Nat -> Nat -> Set where
    leqZ : forall {n}            -> zero  ≤ n
    leqS : forall {n m} -> n ≤ m -> suc n ≤ suc m

  ≤-suc : forall {a b} -> a ≤ b -> a ≤ suc b
  ≤-suc leqZ     = leqZ
  ≤-suc (leqS p) = leqS (≤-suc p)

  plus-≤ : forall a {b c} -> a + b ≤ c -> b ≤ c
  plus-≤ zero    p        = p
  plus-≤ (suc a) (leqS p) = ≤-suc (plus-≤ a p)

  ≤-refl : forall {a} -> a ≤ a
  ≤-refl {zero} = leqZ
  ≤-refl {suc n} = leqS ≤-refl

  -- Recursion over a bound on a (needed for termination).
  divModˢ : forall {size} a b -> a ≤ size -> DivMod a (suc b)
  divModˢ a b prf with boundView (suc b) a
  divModˢ .(toNat r)   b _          | below r = dmZ r
  divModˢ .(suc b + k) b (leqS prf) | above k = dmS (divModˢ k b (plus-≤ b prf))

  divMod : forall a b {nz : NonZero b} -> DivMod a b
  divMod a zero {}
  divMod a (suc b) = divModˢ a b ≤-refl

  -- We ought to prove that the inductive version behaves the same as the
  -- direct version... but that's more work than we're willing to spend.

open Inductive

_div_ : (a b : Nat){nz : NonZero b} -> Nat
_div_ a b {nz} = getQ (divMod a b {nz})

_mod_ : (a b : Nat){nz : NonZero b} -> Nat
_mod_ a b {nz} = getR (divMod a b {nz})


