-- Andreas, 2022-09-19, issue #6108, reported by dolio.
-- Test case by nad.

-- Higher constructors should not be guarding.

{-# OPTIONS --safe --cubical --guardedness #-}

open import Agda.Builtin.Cubical.Path
open import Agda.Primitive.Cubical

mutual

  record R : Set where
    coinductive
    field
      force : D

  data D : Set where
    higher : R.force ≡ R.force

-- This should not be accepted, since `higher i0` reduces to `R.force`.
r : I → R
r i .R.force = higher i (r i)

-- This loops...
loops : ∀ {x : D} → x ≡ r i0 .R.force
loops _ = r i0 .R.force
