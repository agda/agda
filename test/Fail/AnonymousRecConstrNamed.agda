module AnonymousRecConstrNamed where

open import Agda.Builtin.Nat

-- Tests that you can't use Record.constructor syntax if the record has
-- a named constructor.

record Foo : Set where
  constructor foo
  field
    x : Nat

_ : Nat → Foo
_ = Foo.constructor
