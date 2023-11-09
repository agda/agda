module AnonymousRecConstr where

-- Basic test about referring to the constructor of a record with no
-- 'constructor' directive.

open import Agda.Builtin.Nat

record Bar : Set where
  field
    x : Nat

_ : Nat → Bar
_ = Bar.constructor
