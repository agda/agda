-- Andreas, 2026-09-15, issue #8749.
--
-- This is the regression caused by the *simple* fix attempt for #8749, namely
-- eagerly solving the instance constraints that block the expected type in
-- `tryInsertHiddenLambda` (without rolling them back).
--
-- Shrunk from `Cubical/ZCohomology/RingStructure/RingLaws.agda:62`;
-- `Cubical/CW/HurewiczTheorem.agda:758` breaks by the same mechanism.
--
-- The pattern:
--
--   * The expected type of `y` in `op {0} x y` is `K (fromNat 0 ⦃i⦄ ⦃c⦄)`,
--     which is *blocked* on the instance meta `i : Number Nat`.
--
--   * The elaborated `op {0} x y` therefore has the blocked type
--     `K (fromNat 0 ⦃i⦄ ⦃c⦄)`, and that -- still with the head `K` intact --
--     is what `_≡_` picks up for its implicit type argument `A`.
--
--   * The right-hand side `op y x` has type `K ?n`.  Unifying it with
--     `A = K (fromNat 0 ⦃i⦄ ⦃c⦄)` succeeds under `--lossy-unification`
--     (first-order approximation: same head `K`, so unify the arguments),
--     giving `?n := fromNat 0 ⦃i⦄ ⦃c⦄`.
--
-- Solving `i` earlier destroys this: `K (fromNat 0 ⦃numNat⦄ ⦃tt⦄)` now reduces
-- all the way to `Int`, so `A := Int`, the shared head `K` is gone, and
-- `K ?n =< Int` is unsolvable -- `K` is not constructor-headed, so Agda cannot
-- invert it either.  (In the cubical file this shows up as
-- "Refusing to invert pattern matching of coHomK ... maximum depth (50)".)
--
-- This is why the fix must not solve the instance constraints at all: it only
-- *postpones* the type checking problem, leaving the elaboration order -- and
-- thus the shape of the types the unifier sees -- exactly as before.
--
-- Committing the instance solutions is also catastrophic for performance:
-- `Cubical/Cohomology/EilenbergMacLane/Groups/KleinBottle.agda` goes from 8s
-- to not finishing within 40 minutes.

{-# OPTIONS --lossy-unification #-}
-- {-# OPTIONS --experimental-lossy-unification #-}

module Issue8749-lossy-regression where

open import Agda.Builtin.Nat
open import Agda.Builtin.Equality
open import Agda.Builtin.FromNat
open import Agda.Builtin.Unit

postulate Int : Set

-- Like cubical's `coHomK`: `K 0` reduces to something rigid, but `K` itself
-- is not constructor-headed, so Agda cannot invert it.
K : Nat → Set
K zero    = Int
K (suc n) = K n

instance
  numNat : Number Nat
  numNat = record { Constraint = λ _ → ⊤ ; fromNat = λ n → n }

postulate
  op    : (n : Nat) → Int → K n → K n
  works : (x y : Int) → op 0 x y ≡ op _ y x
