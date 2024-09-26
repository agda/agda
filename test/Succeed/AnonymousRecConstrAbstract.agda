module AnonymousRecConstrAbstract where

-- Tests that you can refer to the constructor of an abstract record
-- using Record.constructor syntax as long as you're in AbstractMode.

abstract record Foo : Set₁ where
  field
    x : Set

abstract
  _ : Set → Foo
  _ = Foo.constructor
