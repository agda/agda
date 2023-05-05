-- Andreas, 2019-10-01, continuing issue #3855 (erasure modality @0)
-- Test case by Nisse at https://github.com/agda/agda/issues/3855#issuecomment-527164352

-- Occurs check needs to take erasure status of definitions
-- (here: postulates) into account.

{-# OPTIONS --erasure #-}

postulate
  P    : Set → Set
  p    : (A : Set) → P A
  @0 A : Set

-- fails : P A
-- fails = p A

test : P A
test = p _

-- Should fail with error like:
--
-- Cannot instantiate the metavariable _2 to solution A
-- since (part of) the solution was created in an erased context
-- when checking that the expression p _ has type P A
