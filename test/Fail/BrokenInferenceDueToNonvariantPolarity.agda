-- Andreas, 2012-09-15
{-# OPTIONS --show-implicit #-}
-- {-# OPTIONS -v tc.meta:50 #-}
-- {-# OPTIONS -v tc.conv:50 #-}
-- {-# OPTIONS -v tc.polarity:10 #-}
-- {-# OPTIONS -v tc.constr.findInScope:50 #-}
module BrokenInferenceDueToNonvariantPolarity where

import Common.Level

data ⊥ : Set where
record ⊤ : Set where

data Nat : Set where
  zero : Nat
  suc  : Nat → Nat

False : Nat → Set
False zero    = ⊥
False (suc n) = False n

module Invariant where
  record Bla (n : Nat)(p : False n) : Set where
  -- phantom arguments to Bla get polarity 'Invariant'

module Nonvariant where
  Bla : (n : Nat) → False n → Set
  Bla n p = ⊤
  -- polarity checker infers arguments to be 'Nonvariant'

-- open Invariant  -- succeeds
open Nonvariant -- fails

module Works where

  drop-suc : {n : Nat}{{p : False n}} → Bla (suc n) p → Bla n p
  drop-suc _ = _

  works :  (n : Nat) → {{p : False n}} → Bla n p → ⊥
  works zero {{()}} b
  works (suc n) b = works n (drop-suc {n} b)

module Fails where

  drop-suc : {n : Nat}{{p : False n}} → Bla (suc n) p → Bla n p
  drop-suc _ = _

  bla : (n : Nat) → {p : False n} → Bla n p → ⊥
  bla zero {()} b
  bla (suc n) b = bla n (drop-suc b)
  -- Since Bla is analysed as constant function, the constraint
  -- Bla n p = Bla X Y does not provide unique solutions for X and Y.
  -- And since the positivity checker runs after constraint solving,
  -- Agda does not recognize that bla is Nonvariant in argument p
  -- and that it hence could search for any solution.

