-- Andreas, 2012-07-01, issue reported by patrickATparcs.ath...
-- {-# OPTIONS -v tc.term.let.pattern:20 #-}
module Issue671 where

open import Common.Prelude

record Foo : Set where
  constructor foo
  field
    foo₁ : Nat

bar : Nat → Nat
bar a  = let
     b = a
     c = b
     foo x = foo 5
  in b
-- should succeed, used to throw a panic from Open'ing a let assigned value
-- in a wrong Context
