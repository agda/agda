{-# OPTIONS --double-check #-}
module LetAxiomInstance where

open import Agda.Builtin.Nat

record Foo (A : Set) : Set where
  field
    foo : A

open Foo {{ ... }}

-- Tests that let-axiom instances are correctly picked up by instance
-- search

test : Nat → Nat
test ignored =
  let
    instance x : Foo Nat
  in foo
