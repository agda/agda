-- Andreas, 2018-06-18, problem surfaced with issue #3136
-- Correct printing of a pattern lambda that has no patterns.

-- {-# OPTIONS -v extendedlambda:50 #-}

open import Agda.Builtin.Bool
open import Agda.Builtin.Equality

record R : Set where
  no-eta-equality
  field w : Bool

f : R
f = λ where
  .R.w → λ where
    → false

triggerError : ∀ x → x ≡ f
triggerError x = refl

-- Error prints extended lambda name in error:
-- x != λ { .R.w → λ { .extendedlambda1 → false } } of type R
-- when checking that the expression refl has type x ≡ f

-- Expected:
-- x != λ { .R.w → λ { → false } } of type R
-- when checking that the expression refl has type x ≡ f
