-- Andreas, 2019-06-25, issue #3855 reported by nad
-- Constraint solver needs to respect erasure.

{-# OPTIONS --erasure #-}

open import Agda.Builtin.Bool

module _ where

  record RB (b : Bool) : Set where
    bPar : Bool
    bPar = b

  myBPar : (@0 b : Bool) → RB b → Bool
  myBPar b r = RB.bPar {b = {!b!}} r         -- should be rejected
