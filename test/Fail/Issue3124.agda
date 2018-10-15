-- Andreas, 2018-06-10, issue #3124
-- Wrong context for error IrrelevantDatatype in the coverage checker.

{-# OPTIONS --prop #-}

data Squash (A : Set) : Prop where
  squash : A → Squash A

test : ∀{A} → Squash (Squash A → A)
test = squash λ{ (squash y) → y }

-- WAS: de Bruijn index in error message

-- Expected error:
-- Cannot split on argument of irrelevant datatype (Squash .A)
-- when checking the definition of .extendedlambda0
