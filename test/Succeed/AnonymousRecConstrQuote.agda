module AnonymousRecConstrQuote where

open import Agda.Builtin.Reflection

-- Tests that you can quote a name obtained through Record.constructor
-- syntax.

record Bar : Set₁ where
  field
    x : Set

_ : Name
_ = quote Bar.constructor
