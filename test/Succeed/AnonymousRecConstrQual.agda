module AnonymousRecConstrQual where

open import Agda.Builtin.Nat

-- Tests that Record.constructor syntax works even if the constructor is
-- in scope qualified.

module Foo where
  record Bar : Set where
    field
      x : Nat

_ : Nat → Foo.Bar
_ = Foo.Bar.constructor
