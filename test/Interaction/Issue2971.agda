-- Andreas, 2018-03-19, issue #2971, reported by Ulf
-- Splitting on result should give proper error
-- when record type is weak, i.e. lacks projections.

{-# OPTIONS --no-irrelevant-projections #-}

-- {-# OPTIONS -v tc.cover:20 #-}

open import Agda.Builtin.Nat
open import Agda.Builtin.Equality

record Five : Set where
  field
    five : Nat
    .prf : five ≡ 5  -- No corresponding projection!

best-number : Five
best-number = {!!} -- C-c C-c (on result)

-- Error WAS:
-- Panic: Unbound name: NoIrrProj.Five.prf
-- [0,2,10]@5465979233139828506
-- when checking that the expression ? has type Five

-- Should give proper error message.

-- Cannot split on result here, because record has irrelevant fields,
-- but no corresponding projections
-- when checking that the expression ? has type Five

-- Update, Andreas, 2018-06-09: splitting on irrelevant fields is always ok.
-- Should succeed!


-- Testing similar errors:

not-record : Set
not-record = {!!}

-- Cannot split on result here, because target type  Set  is not a record type
-- when checking that the expression ? has type Set
