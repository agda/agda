-- Andreas, 2026-04-21
-- An inductive no-eta record should count as data, and thus be guarding.

open import Agda.Builtin.Equality

mutual
  record D : Set where
    inductive; no-eta-equality
    field g : R

  record R : Set where
    inductive
    field f : D

test : {r : R} → r ≡ record{ f = R.f r }
test = refl

-- R should have eta, this should succeed.
