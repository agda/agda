-- Andreas, 2026-04-25, PR #8533
-- no-eta-equality records are guarding, like data types

open import Agda.Builtin.Equality

mutual
  record D : Set where
    inductive; no-eta-equality; pattern
    field r : R

  -- no ETA_EQUALITY pragma needed here
  record R : Set where
    inductive; eta-equality
    field d : D

eta-R : {r : R} → r ≡ record { d = R.d r }
eta-R = refl

data ⊥ : Set where

mutual
  empty-D : (d : D) → ⊥
  empty-D record{ r = x } = empty-R x

  empty-R : (r : R) → ⊥
  empty-R record{ d = y } = empty-D y
