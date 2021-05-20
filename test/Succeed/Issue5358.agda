-- Andreas, 2021-05-07, issue #5358 reported by ecavallo
-- Do not expand clauses with tactics attached to the target type!

open import Agda.Builtin.Unit
open import Agda.Builtin.Bool
open import Agda.Builtin.Reflection renaming (bindTC to _>>=_)

defaultTo : {A : Set} (x : A) → Term → TC ⊤
defaultTo x goal = do
  `x ← quoteTC x
  unify goal `x

record Class : Set where
  constructor con
  field
    x : Bool → Bool
    @(tactic defaultTo x) {y} : Bool → Bool
open Class

{- Correctly succeeds -}
testA : Class
testA = con (λ b → b)

{-
  WAS: Incorrectly fails with:
  Bool → Bool !=< Bool
  when checking that the inferred type of an application
    Bool → Bool
  matches the expected type
    Bool

What is happening here?

  - The coverage checker detects a missing clause
    testB .y : @(tactic defaultTo x) {Bool → Bool}.

  - It expands this to testB .y b : @(tactic defaultTo x) {Bool},
    eliminating the function type.

  - It then runs the tactic at the wrong type.

A fix is to not expand the clause if there is a tactic attached to the projections.
-}

testB : Class
testB .x = λ b → b

-- Should succeed
