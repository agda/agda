-- Andreas, 2019-11-10, issue #4185, reported and test case by nad.
--
-- Problem: no-eta-equality was ignored during Miller pattern unification
-- when turning meta-variable applied to constructed record expression
-- into meta-variable applied to record field(s).

-- {-# OPTIONS -v tc.meta.assign:30 #-}

open import Agda.Builtin.Equality

record Box (A : Set) : Set where
  no-eta-equality
  constructor box
  field
    unbox : A

open Box

postulate
  A : Set

AllBox All : (P : Box A → Set) → Set
AllBox P = (x : Box A) → P x
All    P = (a : A) → P (box a)

postulate
  to    : (P : Box A → Set) → AllBox P → All P

  from  : (P : Box A → Set) → All P → AllBox P

  test  : (P : Box A → Set)
        → (f : AllBox P) → from _ (to P f) ≡ f  -- Underscore should be solved.

-- Problem WAS:
--
-- Due to invalid η-expansion, the equation
--
--   _P (box a) = P (box a)
--
-- was solved as
--
--   _P x = P (box (unbox x))
--
-- resulting in a subsequent type error as Box has no η.
