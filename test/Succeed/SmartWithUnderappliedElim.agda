{-# OPTIONS --smart-with #-}

open import Agda.Builtin.Equality
open import Agda.Builtin.Equality.Rewrite
open import Agda.Builtin.Nat

-- Used to reject the second '--smart-with' abstraction, claiming that
-- 'bar test2' was underapplied

record Foo : Set where
  no-eta-equality
  field
    proj : Nat
open Foo

test : Foo
test .proj = 42

test2 : Foo
test2 .proj = 42

postulate
  bar : Foo → Foo

foo : Nat
foo with x ← bar test
    with y ← bar test2
    = 0
