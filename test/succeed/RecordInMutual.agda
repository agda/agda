-- {-# OPTIONS -v tc.pos:100 #-}
-- Records are allowed in mutual blocks.
module RecordInMutual where

import Common.Level
open import Common.Equality

mutual
  record A : Set where
    field p : D
  record B : Set where
    field q : A
  data D : Set where
    c : B -> D

open A
open B

-- A and B are guarded via D, so we have eta for A and for B:

etaA : {a : A} → a ≡ record { p = p a }
etaA = refl

etaB : {b : B} → b ≡ record { q = q b }
etaB = refl
