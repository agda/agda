-- Andreas, 2022-03-07, issue #5809 reported by jamestmartin
-- Regression in Agda 2.6.1.
-- Not reducing irrelevant projections lead to non-inferable elim-terms
-- and consequently to internal errors.
--
-- The fix is to treat irrelevant projections as just functions,
-- retaining their parameters, so that they remain inferable
-- even if not in normal form.

{-# OPTIONS --irrelevant-projections #-}
{-# OPTIONS --allow-unsolved-metas #-}

-- {-# OPTIONS --no-double-check #-}
-- {-# OPTIONS -v impossible:100 #-}
-- {-# OPTIONS -v tc:40 #-}

open import Agda.Builtin.Equality

record Squash {ℓ} (A : Set ℓ) : Set ℓ where
  constructor squash
  field
    .unsquash : A
open Squash

.test : ∀ {ℓ} {A : Set ℓ} (x : A) (y : Squash A) → {!!}
test x y = {!!}
  where
    help : unsquash (squash x) ≡ unsquash y
    help = refl

-- WAS: internal error.
-- Should succeed with unsolved metas.
