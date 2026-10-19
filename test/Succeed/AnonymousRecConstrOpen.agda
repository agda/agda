-- Andreas, 2026-08-24, re issue #8625

module AnonymousRecConstrOpen where

-- Opening a record module does not bring the pseudo-name `constructor`
-- into scope; in particular, it does not add a second name for the
-- record constructor that would make its notation ambiguous.

open import Agda.Builtin.Nat

record R : Set2 where
  constructor mk
  field
    fst snd : Set1

open R public

syntax mk A B = A ⟶ B

_ : R
_ = Set ⟶ Set

_ : (A B : Set1) → R
_ = R.constructor
