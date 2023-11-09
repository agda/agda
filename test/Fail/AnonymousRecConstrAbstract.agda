module AnonymousRecConstrAbstract where

-- Tests that you can't use Record.constructor syntax to bypass
-- 'abstract' hiding the constructor.

abstract record Foo : Set₁ where
  field
    x : Set

_ : Set → Foo
_ = Foo.constructor
