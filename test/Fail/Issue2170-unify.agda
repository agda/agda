{-# OPTIONS --show-irrelevant #-}

module Issue2170-unify where

data _≡_ {A : Set} (x : A) : A → Set where
  refl : x ≡ x

record Squash (A : Set) : Set where
  constructor squash
  field .unsquash : A
open Squash

record UnSquash (A : Set) (s : A → Squash A) : Set where
  constructor inverse
  field
    inv : Squash A → A
    prf : {a : A} → inv (s a) ≡ a

test : {A : Set} → Squash (UnSquash A squash)
test = squash (inverse (λ p@(squash x) → _) refl)

-- `refl` is checked at type `_15 A (squash a) ≡ a`
-- Before, Agda solved this as `_15 := λ A p → unsquash a`, which
-- makes use of the irrelevant projection `unsquash`.
-- However, this is not allowed unless `--irrelevant-projections`
-- is enabled.
