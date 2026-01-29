-- Amy, PR #7572, adding let-bindings without definition (LetAxiom).
-- Andreas, Issue #8344, reported by Johannes Waldmann:
-- LetAxioms should show up in context without a definition.

module LetAxiom where

open import Agda.Builtin.Equality
open import Agda.Builtin.Nat

test : Nat
test =
  let
    x : Nat
  in {!!}  -- C-c C-,

-- Was: not a valid let binding
-- Should be: missing definition, but type checking proceeds

_ : 2 + 2 ≡ 4
_ = refl

-- In the context display (C-c C-,) there should not be any definition for x,
-- only its type.
